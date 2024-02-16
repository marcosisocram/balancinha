/*
 * balance - a balancing tcp proxy
 * $Revision: 3.57 $
 *
 * Copyright (c) 2000-2009,2010 by Thomas Obermair (obermair@acm.org)
 * and Inlab Software GmbH (info@inlab.de), Gruenwald, Germany.
 * All rights reserved.
 *
 * Thanks to Bernhard Niederhammer for the initial idea and heavy
 * testing on *big* machines ...
 *
 * For license terms, see the file COPYING in this directory.
 *
 * This program is dedicated to Richard Stevens...
 *
 *  3.57
 *    MAXGROUPS has been increased to 32
 *  3.56
 *    added out-of-band data handling
 *    thanks to Julian Griffiths
 *  3.54
 *    fixed hash_fold bug regarding incoming IPv4 and IPv6 source addresses
 *  3.52
 *    thanks to David J. Jilk from Standing Cloud, Inc. for the following:
 *    added "nobuffer" functionality to interactive shell IO
 *    added new "assign" interactive command
 *    fixed locking bug
 *  3.50
 *    new option -6 forces IPv6 bind (hints.ai_family = AF_INET6)
 *  3.49
 *    ftok() patch applied (thanks to Vladan Djeric)
 *  3.48
 *    Problems with setting IPV6_V6ONLY socket option are now handled
 *    more nicely with a syslog warning message
 *  3.42
 *    Balance compiles now on systems where IPV6_V6ONLY is undefined
 *  3.35
 *    bugfix in autodisable code (thanks to Michael Durket)
 *  3.34
 *    syslog logging added (finally)
 *    -a autodisable option added (thanks to Mitsuru IWASAKI)
 *  3.33
 *    SO_KEEPALIVE switched on (suggested and implemented by A. Fluegel)
 *    new option -M to use a memory mapped file instead of IPC shared memory
 *  3.32
 *    /var/run/balance may already exist (thanks to Thomas Steudten)
 *  3.31
 *    TCP_NODELAY properly switched on (thanks to Kurt J. Lidl).
 *  3.30
 *    Code cleanups and fixes (thanks to Kurt J. Lidl)
 *  3.28
 *    Code cleanup's (thanks to Thomas Steudten)
 *    MRTG-Interface (thanks to Brian McCann for the suggestion)
 *  3.26
 *    bugfix: master process was not found with balance -i
 *    unused variable pid removed (BSD)
 *  3.24
 *    bugfix in channel/group argument parsing (thanks to Enrique G. Paredes)
 *    permisions+error messages improvements (thanks to Wojciech Sobczuk)
 *  3.22
 *    writelock and channelcount patch from Stoyan Genov
 *    balance exit codes fix from Chris Wilson
 *    /var/run/balance is tried to be autocreated (if not there)
 *    close of 0,1,2 on background operation
 *  3.19
 *    -h changed to -H
 *  3.17
 *    -h option added
 *    thanks to Werner Maier
 *  3.16
 *    fixed missing save_tmout initialization
 *    thanks to Eric Andresen
 *  3.15
 *    first -B support
 *  3.14
 *    -Wall cleanup
 *  3.12
 *    alarm(0) added, thanks to Jon Christensen
 *  3.11
 *    Bugfix
 *  3.10
 *    Bugfix for RedHat 7.2
 *  3.9
 *    Moved rendezvous file to /var/run and cleaned main(), thanks to
 *    Kayne Naughton
 *  3.8
 *    move to sigaction(), thanks to Kayne Naughton
 *  3.5
 *    Select-Timeout, thanks to Jeff Buhlmann
 *  3.2
 *    Hash groups and some other improvements
 *  2.24:
 *    'channel 2 overload' problem fixed, thanks to Ed "KuroiNeko"
 *  2.26:
 *    'endless loop error' fixed, thanks to Anthony Baxter
 *  2.27:
 *    strcmp on NULL removed, thanks to Jay. D. Allen
 *  2.28:
 *    bsent and breceived now unsigned to avoid negative values,
 *    thanks to Anthony Baxter
 *  2.29:
 *    error in setaddress() fixed, thanks to Dirk Datzert
 *  2.30:
 *    fixing #includes for *bsd compability
 *  2.31:
 *  2.32:
 *    redefied SIGCHLD handling to be compatible with FreeBSD 4.3,
 *    BSD/OS 4.2 and BSD/OS 4.0.1
 *  2.33
 *    finally included SO_REUSEADDR
 *
 */

#include <balance.h>
#include <stdio.h>

const char *balance_rcsid = "$Id: balance.c,v 3.7-rinha 2024/01/13 07:49:16 t Exp $";
static char *revision = "$Revision: 3.7-rinha $";

static int release;
static int subrelease;

static char rendezvousfile[FILENAMELEN_T];
static int rendezvousfd;
#ifndef NO_MMAP
static int shmfilefd;
#endif

static int cur_s;
static int cur_r;

static void urg_handler(int signo) {
    printf("urg_handler :: signo %d\n", signo);

    int n;
    char buf[256];

    n = recv(cur_r, buf, sizeof buf, MSG_OOB);
    if (n >= 0) {
        buf[n] = 0;
        // printf("URG '%s' (%d)\n", buf,n);
        send(cur_s, buf, strlen(buf), MSG_OOB);
    }
    signal(SIGURG, urg_handler);
}

static int err_dump(char *text) {
    fprintf(stderr, "balance: %s\n", text);
    fflush(stderr);
    exit(EX_UNAVAILABLE);
}

COMMON *common;

static int hashfailover = 0;
static int foreground = 0;
static int shmmapfile = 0;

static int sockbufsize = 32768;

static int connect_timeout;

static char *bindhost = NULL;

static struct timeval sel_tmout = {0, 0}; /* seconds, microseconds */
static struct timeval save_tmout = {0, 0}; /* seconds, microseconds */

int create_serversocket(char *node, char *service) {
    printf("create_serversocket :: node=%s :: service=%s :: \n", node, service);

    struct addrinfo hints;
    struct addrinfo *results;
    int srv_socket, status, sockopton/*, sockoptoff*/;

    bzero(&hints, sizeof(hints));
    hints.ai_flags = AI_PASSIVE;


    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    status = getaddrinfo(node, service, &hints, &results);
    if (status != 0) {
        fprintf(stderr, "error at getaddrinfo: %s\n", gai_strerror(status));
        fprintf(stderr, "exiting.\n");
        exit(EX_OSERR);
    }

    if (results == NULL) {
        fprintf(stderr, "no matching results at getaddrinfo\n");
        fprintf(stderr, "exiting.\n");
        exit(EX_OSERR);
    }

    srv_socket =
            socket(results->ai_family, results->ai_socktype, results->ai_protocol);

    if (srv_socket < 0) {
        perror("socket()");
        exit(EX_OSERR);
    }

    sockopton = 1;

    status = setsockopt(srv_socket, SOL_SOCKET, SO_REUSEADDR, (char *) &sockopton,
                        sizeof(sockopton));

    if (status < 0) {
        perror("setsockopt(SO_REUSEADDR=1)");
        exit(EX_OSERR);
    }

    status = bind(srv_socket, results->ai_addr, results->ai_addrlen);
    if (status < 0) {
        perror("bind()");
        exit(EX_OSERR);
    }

    status = listen(srv_socket, SOMAXCONN);
    if (status < 0) {
        perror("listen()");
        exit(EX_OSERR);
    }

    return (srv_socket);
}

/* locking ... */

int a_readlock(void) {

    int rc;
    struct flock fdata;
    fdata.l_type = F_RDLCK;
    fdata.l_whence = SEEK_SET;
    fdata.l_start = 0;
    fdata.l_len = 0;
    // fdata.l_sysid=0;
    // fdata.l_pid=0;
repeat:
    if ((rc = fcntl(rendezvousfd, F_SETLKW, &fdata)) < 0) {
        if (errno == EINTR) {
            goto repeat; // 8-)
        } else {
            perror("readlock");
            exit(EX_OSERR);
        }
    }

    // printf("a_readlock :: rc=%d ::\n", rc);
    return (rc);
}

void b_readlock(void) {
    a_readlock();
}

int a_writelock(off_t start, off_t len) {
    int rc;
    struct flock fdata;
    fdata.l_type = F_WRLCK;
    fdata.l_whence = SEEK_SET;

    // fdata.l_start = 0;
    // fdata.l_len = 0;
    fdata.l_start = start;
    fdata.l_len = len;
    // fdata.l_sysid=0;
    // fdata.l_pid=0;
repeat:
    if ((rc = fcntl(rendezvousfd, F_SETLKW, &fdata)) < 0) {

        if (errno == EINTR) {
            goto repeat; // 8-)
        } else {
            perror("a_writelock");
            exit(EX_OSERR);
        }
    }

    return (rc);
}

void b_writelock(void) {
    a_writelock(0, 0);
}

void c_writelock(int group, int channel) {
    a_writelock(((char *) &(grp_channel(common, group, channel))) - (char *) common,
                sizeof(CHANNEL));
}

int a_unlock() {
    int rc;
    struct flock fdata;
    fdata.l_type = F_UNLCK;
    fdata.l_whence = SEEK_SET;
    fdata.l_start = 0;
    fdata.l_len = 0;
    // fdata.l_sysid=0;
    // fdata.l_pid=0;
repeat:
    if ((rc = fcntl(rendezvousfd, F_SETLK, &fdata)) < 0) {
        if (errno == EINTR) {
            goto repeat; // 8-)
        } else {
            perror("a_unlock");
            exit(EX_OSERR);
        }
    }
    return (rc);
}

void b_unlock(void) { a_unlock(0, 0); }

void c_unlock(int group, int channel) {
    a_unlock(((char *) &(grp_channel(common, group, channel))) - (char *) common,
             sizeof(CHANNEL));

}

void *shm_malloc(char *file, int size) {

    char *data = NULL;
    key_t key;
    int shmid;

    // testar passando -M e ver se entra aqui
    if (shmmapfile) {
#ifndef NO_MMAP
        char shmfile[FILENAMELEN];

        strcpy(shmfile, file);
        strcat(shmfile, SHMFILESUFFIX);
        shmfilefd = open(shmfile, O_RDWR | O_CREAT, 0644);
        if (shmfilefd < 0) {
            fprintf(stderr, "Warning: Cannot open file `%s', switching to IPC\n",
                    shmfile);
            shmmapfile = 0;
        }
        if (shmmapfile) {
            if (ftruncate(shmfilefd, size) < 0) {
                fprintf(stderr,
                        "Warning: Cannot set file size on `%s', switching to IPC\n",
                        shmfile);
                close(shmfilefd);
                shmmapfile = 0;
            }
        }
        if (shmmapfile) {
            data = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, shmfilefd, 0);
            if (!data || data == MAP_FAILED) {
                fprintf(stderr, "Warning: Cannot map file `%s', switching to IPC\n",
                        shmfile);
                close(shmfilefd);
                shmmapfile = 0;
            }
        }
#endif
    }

    if (!shmmapfile) {
        if ((key = ftok(file, 'x')) == -1) {
            perror("ftok");
            exit(EX_SOFTWARE);
        }

        if ((shmid = shmget(key, size, 0644 | IPC_CREAT)) == -1) {
            perror("shmget");
            exit(EX_OSERR);
        }

        data = shmat(shmid, (void *) 0, 0);
        if (data == (char *) (-1)) {
            perror("shmat");
            exit(EX_OSERR);
        }
    }

    return (data);
}

int getport(char *port) {

    return atoi(port);
}

void setaddress(struct in_addr *ipaddr, int *port, char *string,
                int default_port, int *maxc) {

    //  char *host_string = NULL;
    char *port_string = NULL;
    char *maxc_string = NULL;
    char *dup_string = NULL;
    char *p = NULL;
    char *q = NULL;

    struct hostent *hent;

    if ((dup_string = strdup(string)) == NULL) {
        fprintf(stderr, "strdup() failed\n");
        exit(EX_OSERR);
    }

    //  host_string = dup_string;
    p = index(dup_string, ':');

    if (p != NULL) {
        *p = '\000';
        port_string = p + 1;
        if ((q = index(port_string, ':')) != NULL) {
            *q = '\000';
            maxc_string = q + 1;
        } else {
            maxc_string = "";
        }
    } else {
        port_string = "";
        maxc_string = "";
    }

    // fix for RedHat 7.0/7.1 choke on strcmp with NULL

    if (port_string != NULL && !strcmp(port_string, ""))
        port_string = NULL;
    if (maxc_string != NULL && !strcmp(maxc_string, ""))
        maxc_string = NULL;

    hent = gethostbyname(dup_string);
    if (hent == NULL) {
        if ((ipaddr->s_addr = inet_addr(dup_string)) == INADDR_NONE) {
            fprintf(stderr, "unknown or invalid address [%s]\n", dup_string);
            exit(EX_DATAERR);
        }
    } else {
        memcpy(ipaddr, hent->h_addr, hent->h_length);
    }
print("")
    *port = getport(port_string);

    if (maxc_string != NULL) {
        *maxc = atoi(maxc_string);
    }
    free(dup_string);
}

int forward(int fromfd, int tofd, int groupindex, int channelindex) {
    ssize_t rc;
    unsigned char buffer[MAXTXSIZE];

    cur_s = tofd;
    cur_r = fromfd;

    signal(SIGURG, &urg_handler);



    fcntl(fromfd, F_SETOWN, getpid());
    rc = recv(fromfd, buffer, MAXTXSIZE, 0);


    if (rc <= 0) {
        return (-1);
    } else {
        if (writen(tofd, buffer, rc) != rc) {
            return (-1);
        }
        c_writelock(groupindex, channelindex);
        chn_bsent(common, groupindex, channelindex) += rc;
        c_unlock(groupindex, channelindex);
    }
    return (0);
}

int backward(int fromfd, int tofd, int groupindex, int channelindex) {


    ssize_t rc;
    unsigned char buffer[MAXTXSIZE];
    rc = read(fromfd, buffer, MAXTXSIZE);

    if (rc <= 0) {
        return (-1);
    } else {
        if (writen(tofd, buffer, rc) != rc) {
            return (-1);
        }
        c_writelock(groupindex, channelindex);
        chn_breceived(common, groupindex, channelindex) += rc;
        c_unlock(groupindex, channelindex);
    }
    return (0);
}

/*
 * the connection is really established, let's transfer the data
 *  as efficient as possible :-)
 */

void stream2(int clientfd, int serverfd, int groupindex, int channelindex) {

    fd_set readfds;
    int fdset_width;
    int sr;
    int optone = 1;

    fdset_width = ((clientfd > serverfd) ? clientfd : serverfd) + 1;

    /* failure is acceptable */
    (void) setsockopt(serverfd, IPPROTO_TCP, TCP_NODELAY, (char *) &optone,
                      (socklen_t) sizeof(optone));
    (void) setsockopt(clientfd, IPPROTO_TCP, TCP_NODELAY, (char *) &optone,
                      (socklen_t) sizeof(optone));
    (void) setsockopt(serverfd, SOL_SOCKET, SO_KEEPALIVE, (char *) &optone,
                      (socklen_t) sizeof(optone));
    (void) setsockopt(clientfd, SOL_SOCKET, SO_KEEPALIVE, (char *) &optone,
                      (socklen_t) sizeof(optone));

    for (;;) {
        FD_ZERO(&readfds);
        FD_SET(clientfd, &readfds);
        FD_SET(serverfd, &readfds);
        /*
         * just in case this system modifies the timeout values,
         * refresh the values from a saved copy of them.
         */
        sel_tmout = save_tmout;

        for (;;) {

            sr = select(fdset_width, &readfds, NULL, NULL, NULL);

            if ((save_tmout.tv_sec || save_tmout.tv_usec) && !sr) {
                c_writelock(groupindex, channelindex);
                chn_c(common, groupindex, channelindex) -= 1;
                c_unlock(groupindex, channelindex);
                fprintf(stderr, "timed out after %d seconds\n", (int) save_tmout.tv_sec);
                exit(EX_UNAVAILABLE);
            }
            if (sr < 0 && errno != EINTR) {

                c_writelock(groupindex, channelindex);
                chn_c(common, groupindex, channelindex) -= 1;
                c_unlock(groupindex, channelindex);
                err_dump("select error");
            }
            if (sr > 0)
                break;
        }

        if (FD_ISSET(clientfd, &readfds)) {
            if (forward(clientfd, serverfd, groupindex, channelindex) < 0) {
                break;
            }
        } else {
            if (backward(serverfd, clientfd, groupindex, channelindex) < 0) {
                break;
            }
        }
    }
    c_writelock(groupindex, channelindex);
    chn_c(common, groupindex, channelindex) -= 1;
    c_unlock(groupindex, channelindex);
    exit(EX_OK);
}

void alrm_handler(int signo) {
}

void usr1_handler(int signo) {
}

void chld_handler(int signo) {
    int status;
    while (waitpid(-1, &status, WNOHANG) > 0);
}

/*
 * a channel in a group is selected and we try to establish a connection
 */

void *stream(int arg, int groupindex, int index, char *client_address,
             int client_address_size) {

    int startindex;
    int sockfd;
    int clientfd;
    struct sigaction alrm_action;
    struct sockaddr_in serv_addr;

    startindex = index; // lets keep where we start...
    clientfd = arg;

    for (;;) {
        if ((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0) {
            err_dump("can't open stream socket");
        }

        (void) setsockopt(sockfd, SOL_SOCKET, SO_SNDBUF, &sockbufsize,
                          sizeof(sockbufsize));
        (void) setsockopt(sockfd, SOL_SOCKET, SO_RCVBUF, &sockbufsize,
                          sizeof(sockbufsize));

        b_readlock();
        bzero((char *) &serv_addr, sizeof(serv_addr));
        serv_addr.sin_family = AF_INET;
        serv_addr.sin_addr.s_addr = chn_ipaddr(common, groupindex, index).s_addr;
        serv_addr.sin_port = htons(chn_port(common, groupindex, index));
        b_unlock();

        alrm_action.sa_handler = alrm_handler;
        alrm_action.sa_flags = 0; // don't restart !
        sigemptyset(&alrm_action.sa_mask);
        sigaction(SIGALRM, &alrm_action, NULL);
        alarm(connect_timeout);

        if (connect(sockfd, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) < 0) {
            /* here we've received an error (either 'timeout' or 'connection refused')
             * let's start some magical failover mechanisms
             */

            c_writelock(groupindex, index);
            chn_c(common, groupindex, index)--;
            c_unlock(groupindex, index);

            b_readlock();
            for (;;) {
                for (;;) {
                    if (grp_type(common, groupindex) == GROUP_RR || hashfailover == 1) {
                        index++;
                        if (index >= grp_nchannels(common, groupindex)) {
                            index = 0;
                        }
                        if (index == startindex) {
                            index = -1; // Giveup
                            break;
                        }
                        if (chn_status(common, groupindex, index) == 1 &&
                            (chn_maxc(common, groupindex, index) == 0 ||
                             (chn_c(common, groupindex, index) <
                              chn_maxc(common, groupindex, index)))) {
                            break; // new index found
                        } else {
                            continue;
                        }
                    } else {
                        err_dump("PANIC: invalid group in stream()");
                    }
                }

                if (index >= 0) {
                    // neuer index in groupindex-group found...
                    break;
                }
            again:
                groupindex++;
                if (groupindex >= MAXGROUPS) {
                    // giveup, index=-1.
                    break;
                }
                if (grp_type(common, groupindex) == GROUP_RR) {
                    if (grp_nchannels(common, groupindex) > 0) {
                        index = grp_current(common, groupindex);
                        startindex =
                                index; // This fixes the "endless loop error"
                        // with all hosts being down and one
                        // in the last group... (from Anthony Baxter)
                    } else {
                        goto again;
                    }
                    break;
                }
                err_dump("PANIC: invalid group in stream()");
            }
            // we drop out here with a new index

            b_unlock();

            if (index >= 0) {
                // lets try it again
                close(sockfd);
                c_writelock(groupindex, index);
                chn_c(common, groupindex, index) += 1;
                chn_tc(common, groupindex, index) += 1;
                c_unlock(groupindex, index);
                continue;
            } else {
                break;
            }
        } else {
            alarm(0); // Cancel the alarm since we successfully connected
            // this prevents the 'channel 2 overload problem'

            // b_writelock();
            a_writelock(0, 0);
            grp_current(common, groupindex) = index;
            grp_current(common, groupindex)++;
            if (grp_current(common, groupindex) >=
                grp_nchannels(common, groupindex)) {
                grp_current(common, groupindex) = 0;
            }
            b_unlock();

            // everything's fine ...

            stream2(clientfd, sockfd, groupindex, index);
            printf("main :: stream2 retornou\n");

            // stream2 bekommt den Channel-Index mit
            // stream2 never returns, but just in case...
            break;
        }
    }

    close(sockfd);
    exit(EX_OK);
}

static void initialize_release_variables(void) {
    char *version;
    char *revision_copy;
    char *token;

    if ((revision_copy = (char *) malloc(strlen(revision) + 1)) == NULL) {
        fprintf(stderr, "malloc problem in initialize_release_variables()\n");
    } else {
        strcpy(revision_copy, revision);
        token = strtok(revision_copy, " ");
        token = strtok(NULL, " ");
        version = token != NULL ? token : "0.0";
        release = atoi(version);
        if (strlen(version) >= 3) {
            subrelease = atoi(version + 2);
        } else {
            subrelease = 0;
        }
        free(revision_copy);
    }
}

COMMON *makecommon(int argc, char **argv, int source_port) {
    int i;
    int group;
    int channel;
    COMMON *mycommon;
    int numchannels = argc - 1; // port number is first argument

    if (numchannels >= MAXCHANNELS) {
        fprintf(stderr, "MAXCHANNELS exceeded...\n");
        exit(EX_USAGE);
    }

    if ((rendezvousfd = open(rendezvousfile, O_RDWR, 0)) < 0) {
        perror("open");
        fprintf(stderr, "check rendezvousfile permissions [%s]\n", rendezvousfile);
        exit(EX_NOINPUT);
    }

    b_writelock();

    if ((mycommon = (COMMON *) shm_malloc(rendezvousfile, sizeof(COMMON))) ==
        NULL) {
        fprintf(stderr, "cannot alloc COMMON struct\n");
        exit(EX_OSERR);
    }

    mycommon->pid = getpid();
    mycommon->release = release;
    mycommon->subrelease = subrelease;

    for (group = 0; group < MAXGROUPS; group++) {
        grp_nchannels(mycommon, group) = 0;
        grp_current(mycommon, group) = 0;
        grp_type(mycommon, group) = GROUP_RR; // Default: RR
    }

    group = 0;
    channel = 0;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "!")) {
            // This is a normal "GROUP_RR"-Type of Group
            if (channel <= 0) {
                err_dump("no channels in group");
            }
            grp_type(mycommon, group) = GROUP_RR;
            group++;
            channel = 0;
            if (group >= MAXGROUPS) {
                err_dump("too many groups");
            }
        } else if (!strcmp(argv[i], "%")) {
            // This is a "GROUP_HASH"
            if (channel <= 0) {
                err_dump("no channels in group");
            }
            grp_type(mycommon, group) = GROUP_HASH;
            group++;
            channel = 0;
            if (group >= MAXGROUPS) {
                err_dump("too many groups");
            }
        } else {
            chn_status(mycommon, group, channel) = 1;
            chn_c(mycommon, group, channel) = 0; // connections...
            chn_tc(mycommon, group, channel) = 0; // total connections...
            chn_maxc(mycommon, group, channel) = 0; // maxconnections...
            setaddress(&chn_ipaddr(mycommon, group, channel),
                       &chn_port(mycommon, group, channel), argv[i], source_port,
                       &chn_maxc(mycommon, group, channel));
            chn_bsent(mycommon, group, channel) = 0;
            chn_breceived(mycommon, group, channel) = 0;

            grp_nchannels(mycommon, group) += 1;
            channel++;
            if (channel >= MAXCHANNELS) {
                err_dump("too many channels in one group");
            }
        }
    }


    b_unlock();
    return (mycommon);
}

int mycmp(char *s1, char *s2) {
    int l;
    l = strlen(s1) < strlen(s2) ? strlen(s1) : strlen(s2);
    if (strlen(s1) > strlen(s2)) {
        return (!1);
    } else {
        return (!strncmp(s1, s2, l));
    }
}

char bindhost_address[FILENAMELEN];

int main(int argc, char *argv[]) {



    int sockfd, newsockfd, childpid;
    unsigned int clilen;

    int source_port = 9999; // 9999 porta padrão da rinha de backend
    int fd;

    struct stat buffer;
    struct sockaddr_storage cli_addr;
    struct sigaction usr1_action, chld_action;
#ifdef BalanceBSD
#else
    struct rlimit r;
#endif

    connect_timeout = DEFAULTTIMEOUT;
    initialize_release_variables();

    bindhost = optarg;
    foreground = 1;

#ifdef NO_MMAP
  fprintf(stderr,
          "Warning: Built without memory mapped file support, using IPC\n");
#else
    shmmapfile = 1;
#endif

    argc -= optind;
    argv += optind;

    usr1_action.sa_handler = usr1_handler;
    usr1_action.sa_flags = SA_RESTART;
    sigemptyset(&usr1_action.sa_mask);
    sigaction(SIGUSR1, &usr1_action, NULL);

    chld_action.sa_handler = chld_handler;
    chld_action.sa_flags = SA_RESTART;
    sigemptyset(&chld_action.sa_mask);
    sigaction(SIGCHLD, &chld_action, NULL);
    // really dump core if something fails...

#ifdef BalanceBSD
#else
    getrlimit(RLIMIT_CORE, &r);
    r.rlim_cur = r.rlim_max;
    setrlimit(RLIMIT_CORE, &r);
#endif

    snprintf(bindhost_address, FILENAMELEN, "%s", "0.0.0.0");

    stat(SHMDIR, &buffer);
    if (!S_ISDIR(buffer.st_mode)) {
        mode_t old = umask(0);
        if (mkdir(SHMDIR, 01777) < 0) {
            if (errno != EEXIST) {
                fprintf(stderr,
                        "ERROR: rendezvous directory not available and/or creatable\n");
                fprintf(stderr, "       please create %s with mode 01777 like this: \n",
                        SHMDIR);
                fprintf(stderr, "       # mkdir -m 01777 %s\n", SHMDIR);
                umask(old);
                exit(EX_UNAVAILABLE);
            }
        }
        umask(old);
    }

    sprintf(rendezvousfile, "%sbalance.%d.%s", SHMDIR, source_port,
            bindhost_address);

    if (stat(rendezvousfile, &buffer) == -1) {
        // File not existing yet ...
        if ((fd = open(rendezvousfile, O_CREAT | O_RDWR, 0666)) == -1) {
            fprintf(stderr, "cannot create rendezvous file %s\n", rendezvousfile);
            exit(EX_OSERR);
        } else {

            close(fd);
        }
    }

    openlog("Balance", LOG_ODELAY | LOG_PID | LOG_CONS, LOG_DAEMON);

    /*  Open a TCP socket (an Internet stream socket). */

    sockfd = create_serversocket(bindhost, argv[0]);

    (void) setsockopt(sockfd, SOL_SOCKET, SO_SNDBUF, &sockbufsize,
                      sizeof(sockbufsize));
    (void) setsockopt(sockfd, SOL_SOCKET, SO_RCVBUF, &sockbufsize,
                      sizeof(sockbufsize));

    // init of common (*after* bind())


    common = makecommon(argc, argv, source_port);

    for (;;) {
        int index;
        //    unsigned int uindex;
        int groupindex = 0; // always start at groupindex 0

        clilen = sizeof(cli_addr);

        newsockfd = accept(sockfd, (struct sockaddr *) &cli_addr, &clilen);
        if (newsockfd < 0) {

            continue;
        }

        /*
         * the balancing itself:
         * - groupindex = 0
         * - decision which channel to use for the first try
         * - client address available in cli_addr
         *
         */

        b_writelock();
        a_writelock(0, 0);
        for (;;) {
            index = grp_current(common, groupindex);
            for (;;) {
                if (grp_type(common, groupindex) == GROUP_RR) {
                    if (chn_status(common, groupindex, index) == 1 &&
                        (chn_maxc(common, groupindex, index) == 0 ||
                         (chn_c(common, groupindex, index) <
                          chn_maxc(common, groupindex, index)))) {
                        break; // channel found
                    } else {
                        index++;
                        if (index >= grp_nchannels(common, groupindex)) {
                            index = 0;
                        }
                        if (index == grp_current(common, groupindex)) {
                            index = -1; // no channel available in this group
                            break;
                        }
                    }
                } else {
                    err_dump("PANIC: invalid group type");
                }
            }

            // Hier fallen wir "raus" mit dem index in der momentanen Gruppe, oder -1
            // wenn nicht moeglich in dieser Gruppe

            grp_current(common, groupindex) = index;
            grp_current(common, groupindex)++; // current index dieser gruppe wieder
            // null, wenn vorher ungueltig (-1)

            // Der index der gruppe wird neu berechnet und gespeichert, "index" ist
            // immer noch -1 oder der zu waehlende index...

            if (grp_current(common, groupindex) >=
                grp_nchannels(common, groupindex)) {
                grp_current(common, groupindex) = 0;
            }

            if (index >= 0) {
                chn_c(common, groupindex,
                      index)++; // we promise a successful connection
                chn_tc(common, groupindex,
                       index)++; // also incrementing the total count
                // c++
                break; // index in this group found
            } else {
                groupindex++; // try next group !
                if (groupindex >= MAXGROUPS) {
                    break; // end of groups...
                }
            }
        }

        b_unlock();

        if (index >= 0) {
            if ((childpid = fork()) < 0) {
                // the connection is rejected if fork() returns error,
                // but main process stays alive !

                //        if (debugflag) {
                //          fprintf(stderr, "fork error\n");
                //        }
            } else if (childpid == 0) {
                // child process
                close(sockfd); // close original socket

                // FIX: "#8 SIGPIPE causes unclosed channels"

                signal(SIGPIPE, SIG_IGN);

                // process the request:

                stream(newsockfd, groupindex, index, (char *) &cli_addr, clilen);
                printf("main :: stream=returned ::\n");
                exit(EX_OK);
            }
        }

        close(newsockfd); // parent process
    }
}

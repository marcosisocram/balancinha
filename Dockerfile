FROM alpine:3.19.1 as builder

RUN apk add --no-cache build-base make
WORKDIR /app

COPY . .
RUN make clean balance


FROM alpine:3.19.1

WORKDIR /app
COPY --from=builder /app/balance /app/balance

CMD ["/app/balance"]
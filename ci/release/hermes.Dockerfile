# informalsystems/hermes image
#
# Used for running hermes in docker containers
#
# Usage:
#   docker build . --build-arg TAG=v0.3.0 -t informalsystems/hermes:0.3.0 -f hermes.Dockerfile

FROM rust:1-buster AS build-env

ARG TAG
WORKDIR /root

RUN git clone https://github.com/informalsystems/hermes
RUN cd hermes && git checkout $TAG && cargo build --release


FROM debian:buster-slim
LABEL maintainer="hello@informal.systems"

RUN apt update && apt install -y libssl-dev

RUN useradd -m hermes -s /bin/bash
WORKDIR /home/hermes
USER hermes:hermes
ENTRYPOINT ["/usr/bin/hermes"]

COPY --chown=0:0 --from=build-env /root/hermes/target/release/hermes /usr/bin/hermes
COPY --chown=0:0 --from=build-env /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/ca-certificates.crt

#
# Used for running hermes in docker containers
#
# Usage:
#   docker build . --build-arg TAG=v0.3.0 -t informalsystems/hermes:0.3.0 -f hermes.Dockerfile

FROM rust:1-buster AS build-env

ARG TAG
WORKDIR /root

RUN git clone -b ${TAG} --depth 1 https://github.com/informalsystems/hermes \
 && cd hermes \
 && cargo build --release

FROM ubuntu:rolling
LABEL maintainer="hello@informal.systems"
RUN useradd -m hermes -s /bin/bash
WORKDIR /home/hermes
USER hermes:hermes
ENTRYPOINT ["/usr/bin/hermes"]

COPY --chown=0:0 --from=build-env /usr/lib/x86_64-linux-gnu/libssl.so.1.1 /usr/lib/x86_64-linux-gnu/libssl.so.1.1
COPY --chown=0:0 --from=build-env /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1 /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1
COPY --chown=0:0 --from=build-env /root/hermes/target/release/hermes /usr/bin/hermes

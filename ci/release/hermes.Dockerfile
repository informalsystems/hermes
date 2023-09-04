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

FROM ubuntu:latest
LABEL maintainer="hello@informal.systems"
ARG UID=1000
ARG GID=1000

RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates
RUN update-ca-certificates
RUN groupadd -g ${GID} hermes && useradd -l -m hermes -s /bin/bash -u ${UID} -g ${GID}

WORKDIR /home/hermes
USER hermes:hermes
ENTRYPOINT ["/usr/bin/hermes"]

COPY --chown=0:0 --from=build-env /root/hermes/target/release/hermes /usr/bin/hermes

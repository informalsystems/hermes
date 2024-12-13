# Used for running Hermes in Docker containers
#
# Usage: (from the root of the working copy)
#   $ docker build . -t informalsystems/hermes -f ci/release/hermes.Dockerfile

FROM rust:1-buster AS build-env

ARG TAG

WORKDIR /root

COPY . .
RUN cargo build --release

FROM ubuntu:latest
LABEL maintainer="hello@informal.systems"
ARG UID=2000
ARG GID=2000

RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates
RUN update-ca-certificates
RUN groupadd -g ${GID} hermes && useradd -l -m hermes -s /bin/bash -u ${UID} -g ${GID}

WORKDIR /home/hermes
USER hermes:hermes
ENTRYPOINT ["/usr/bin/hermes"]

COPY --chown=hermes:hermes --from=build-env /root/target/release/hermes /usr/bin/hermes

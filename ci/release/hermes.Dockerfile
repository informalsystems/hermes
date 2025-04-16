# Used for running Hermes in Docker containers
#
# Usage: (from the root of the working copy)
#   $ docker build . -t informalsystems/hermes -f ci/release/hermes.Dockerfile

FROM rust:1-bookworm AS build-env

ARG TAG
ARG PROTOC_VERSION=28.3

WORKDIR /root

# Install protoc
RUN ARCH=$(uname -m) && \
    if [ "$ARCH" = "x86_64" ]; then \
        ARCH=x86_64; \
    elif [ "$ARCH" = "aarch64" ]; then \
        ARCH=aarch_64;\
    else \
        echo "Unsupported architecture: $ARCH"; exit 1; \
    fi && \
    wget https://github.com/protocolbuffers/protobuf/releases/download/v$PROTOC_VERSION/protoc-$PROTOC_VERSION-linux-$ARCH.zip -O /tmp/protoc.zip && \
    unzip /tmp/protoc.zip -d /usr/local && \
    rm -rf /tmp/protoc.zip

RUN apt update && apt install -y clang libssl-dev pkg-config

COPY . .

RUN cargo build --release

FROM ubuntu:latest
LABEL maintainer="hello@informal.systems"
ARG UID=2000
ARG GID=2000

RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates wget
RUN update-ca-certificates
RUN groupadd -g ${GID} hermes && useradd -l -m hermes -s /bin/bash -u ${UID} -g ${GID}

WORKDIR /home/hermes

RUN ARCH=$(uname -m) && \
    if [ "$ARCH" = "x86_64" ]; then \
        DEB_URL=http://archive.ubuntu.com/ubuntu/pool/main/o/openssl/libssl1.1_1.1.1f-1ubuntu2.23_amd64.deb; \
    elif [ "$ARCH" = "aarch64" ]; then \
        DEB_URL=http://ports.ubuntu.com/pool/main/o/openssl/libssl1.1_1.1.1f-1ubuntu2_arm64.deb; \
    else \
        echo "Unsupported architecture: $ARCH"; exit 1; \
    fi && \
    wget $DEB_URL -O /tmp/libssl1.1.deb && \
    dpkg -i /tmp/libssl1.1.deb && \
    rm -rf /tmp/libssl1.1.deb

USER hermes:hermes
ENTRYPOINT ["/usr/bin/hermes"]
COPY --chown=hermes:hermes --from=build-env /root/target/release/hermes /usr/bin/hermes

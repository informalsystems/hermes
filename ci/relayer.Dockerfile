#####################################################
####         Relayer image for e2e testing       ####
#####################################################
FROM rust:buster AS build-env

ARG CHECKOUT=master
WORKDIR /root

RUN git clone https://github.com/informalsystems/ibc-rs
RUN cd ibc-rs && git checkout $CHECKOUT && cargo build --release

FROM ubuntu:20.04
LABEL maintainer="hello@informal.systems"

ARG RELEASE

# Add Python 3
RUN apt-get update -y && apt-get install python3 python3-toml -y

# Copy relayer executable
COPY --chown=0:0 --from=build-env /usr/lib/x86_64-linux-gnu/libssl.so.1.1 /usr/lib/x86_64-linux-gnu/libssl.so.1.1
COPY --chown=0:0 --from=build-env /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1 /usr/lib/x86_64-linux-gnu/libcrypto.so.1.1
COPY --chown=0:0 --from=build-env /root/ibc-rs/target/release/hermes /usr/bin/hermes

# Relayer folder
WORKDIR /relayer

# Copy configuration file
COPY ci/simple_config.toml .

# Copy setup script
COPY ci/e2e.sh .

# Copy end-to-end testing script
COPY e2e ./e2e

# Copy key files
COPY ci/chains/gaia/$RELEASE/ibc-0/key_seed.json  ./key_seed_ibc-0.json
COPY ci/chains/gaia/$RELEASE/ibc-1/key_seed.json  ./key_seed_ibc-1.json
# COPY ci/chains/gaia/$RELEASE/ibc-0/user2_seed.json ./user2_seed_ibc-0.json
# COPY ci/chains/gaia/$RELEASE/ibc-1/user2_seed.json ./user2_seed_ibc-1.json

# Make it executable
RUN chmod +x e2e.sh

ENTRYPOINT ["/bin/sh"]

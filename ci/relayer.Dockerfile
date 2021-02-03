#####################################################
####                 Relayer image               ####
#####################################################
FROM rust:slim
LABEL maintainer="hello@informal.systems"

ARG RELEASE

WORKDIR /repo

# Add Python 3
RUN apt-get update -y && apt-get install python3 -y

# Copy relayer executable
COPY ./hermes /usr/bin/hermes

# Relayer folder
WORKDIR /relayer

# Copy configuration file
COPY ci/simple_config.toml .

# Copy setup script
COPY ci/e2e.sh .

# Copy end-to-end testing script
COPY e2e ./e2e

# Copy key files
COPY ci/chains/gaia/$RELEASE/ibc-0/key_seed.json ./key_seed_ibc-0.json
COPY ci/chains/gaia/$RELEASE/ibc-1/key_seed.json ./key_seed_ibc-1.json

# Make it executable
RUN chmod +x e2e.sh

ENTRYPOINT ["/bin/sh"]

#####################################################
####                 Build image                 ####
#####################################################
FROM rust:slim AS build-env

# Output Rust version
RUN cargo --version

# Set working dir
WORKDIR /repo

# Copy project files
COPY . .

# Build files
RUN cargo build --workspace --all --release

#####################################################
####                 Relayer image               ####
#####################################################
FROM rust:slim

ARG RELEASE

# Copy relayer executable
COPY --from=build-env /repo/target/release/relayer /usr/bin/rrly

# Relayer folder
WORKDIR /relayer

# Copy configuration file
COPY ci/simple_config.toml .

# Copy setup script
COPY ci/setup_relayer.sh .

# Copy key files
COPY ci/chains/gaia/$RELEASE/ibc0/key_seed.json ./key_seed_ibc0.json
COPY ci/chains/gaia/$RELEASE/ibc1/key_seed.json ./key_seed_ibc1.json

# Make it executable
RUN chmod +x setup_relayer.sh

ENTRYPOINT ["/bin/sh"]

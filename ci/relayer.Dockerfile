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
RUN cargo build --workspace --all

#####################################################
####                 Relayer image               ####
#####################################################
FROM rust:slim

# Copy relayer executable
COPY --from=build-env /repo/target/debug/rrly /usr/bin/rrly

ENV RELAYER /relayer

WORKDIR $RELAYER

# Copy configuration file
COPY ci/simple_config.toml .

# Copy setup script
COPY ci/setup_relayer.sh .

# Make it executable
RUN chmod +x setup_relayer.sh

# Entrypoint
ENTRYPOINT ["/bin/sh", "-c", "/relayer/setup_relayer.sh"]

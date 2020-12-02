#####################################################
####                 Build image                 ####
#####################################################
FROM rust:slim AS build-env

# Output Rust version
RUN cargo --version

# Set working dir
WORKDIR /repo

# Logic to cache cargo dependecies across builds
COPY Cargo.lock .
COPY Cargo.toml .
COPY modules/Cargo.toml /repo/modules/Cargo.toml
COPY proto/Cargo.toml /repo/proto/Cargo.toml
COPY relayer/Cargo.toml /repo/relayer/Cargo.toml
COPY relayer-cli/Cargo.toml /repo/relayer-cli/Cargo.toml
RUN mkdir .cargo
RUN cargo vendor > .cargo/config

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

COPY /repo/vendor /vendor

# Copy configuration file
COPY ci/simple_config.toml .

# Copy setup script
COPY ci/setup_relayer.sh .

# Make it executable
RUN chmod +x setup_relayer.sh

# Entrypoint
ENTRYPOINT ["/bin/sh", "-c", "/relayer/setup_relayer.sh"]

# Build image
FROM golang:alpine AS build-env

# Add dependencies
RUN apk add --no-cache curl make git libc-dev bash gcc linux-headers eudev-dev python3

# Gaia Branch or Release
ARG release

# Clone repository
RUN git clone https://github.com/cosmos/gaia /go/src/github.com/cosmos/gaia

# Set working directory for the build
WORKDIR /go/src/github.com/cosmos/gaia

# Checkout branch (TODO make this a parameter)
RUN git checkout $release

# Install minimum necessary dependencies, build Cosmos SDK, remove packages
RUN apk add --no-cache $PACKAGES && \
    make tools && \
    make install

# Show version
RUN gaiad version --long

# Final image
FROM alpine:edge

ENV GAIA /gaia

# Install ca-certificates
RUN apk add --update ca-certificates

# Add dependenncies
RUN apk add --no-cache tree

RUN addgroup gaia && \
    adduser -S -G gaia gaia -h "$GAIA"

USER gaia

WORKDIR $GAIA

# Copy over binaries from the build-env
COPY --from=build-env /go/bin/gaiad /usr/bin/gaiad
COPY --from=build-env /go/bin/gaiad /usr/bin/tree

# Copy bootstrap script
COPY bootstrap_gaia.sh .

# Set root to change permission
USER root

# Make it executable
RUN chmod +x bootstrap_gaia.sh

# Revert to gaia user
USER gaia

# Entrypoint
ENTRYPOINT ["/bin/sh", "-c", "/gaia/bootstrap_gaia.sh"]
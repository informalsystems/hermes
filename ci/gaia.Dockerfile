###################################################################################################
# Build image
###################################################################################################
FROM golang:alpine AS build-env

# Add dependencies
RUN apk add --no-cache curl make git libc-dev bash gcc linux-headers eudev-dev python3

# Gaia Branch or Release
ARG RELEASE

# Clone repository
RUN git clone https://github.com/cosmos/gaia /go/src/github.com/cosmos/gaia

# Set working directory for the build
WORKDIR /go/src/github.com/cosmos/gaia

# Checkout branch
RUN git checkout $RELEASE

# Build and install Gaia
RUN make install

# Show version
RUN gaiad version --long

###################################################################################################
# Final image
###################################################################################################
FROM alpine:edge
LABEL maintainer="hello@informal.systems"

# Add jq for debugging
RUN apk add --no-cache jq curl

# Copy over binaries from the build-env
COPY --from=build-env /go/bin/gaiad /usr/bin/gaiad

# Copy entrypoint script
COPY ./run-gaiad.sh /usr/bin
RUN chmod 755 /usr/bin/run-gaiad.sh

ENTRYPOINT "/bin/sh"

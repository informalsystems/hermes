#!/usr/bin/env bash

## Programmatic list for creating Gaia Hub chains for testing IBC.
## Instead of blindly running this code, read it line by line and understand the dependecies and tasks.
## Prerequisites: Log into Docker Hub
set -eou pipefail
GAIA_BRANCH="v3.0.0" # Requires a version with the `--keyring-backend` option. v2.1 and above.

echo "*** Building config folders"
MONIKER=node_ibc_0 \
CHAIN_ID=ibc-0 \
CHAIN_IP=172.25.0.10 \
CHAIN_HOME=./chains/gaia/$GAIA_BRANCH/ibc-0 \
RPC_PORT=26657 \
GRPC_PORT=9090 \
CHAIN_SAMOLEANS=100000000000 \
./bootstrap_gaia.sh

MONIKER=node_ibc_1 \
CHAIN_ID=ibc-1 \
CHAIN_IP=172.25.0.11 \
CHAIN_HOME=./chains/gaia/$GAIA_BRANCH/ibc-1 \
RPC_PORT=26657 \
GRPC_PORT=9090 \
./bootstrap_gaia.sh

echo "*** Requirements"
which docker

echo "*** Create Docker image and upload to Docker Hub"
docker build --build-arg CHAIN=gaia --build-arg RELEASE=$GAIA_BRANCH --build-arg NAME=ibc-0 -f --no-cache -t informaldev/ibc-0:$GAIA_BRANCH -f gaia.Dockerfile .
docker build --build-arg CHAIN=gaia --build-arg RELEASE=$GAIA_BRANCH --build-arg NAME=ibc-1 -f --no-cache -t informaldev/ibc-1:$GAIA_BRANCH -f gaia.Dockerfile .

read -p "Press ENTER to push image to Docker Hub or CTRL-C to cancel. " dontcare
docker push informaldev/ibc-0:$GAIA_BRANCH
docker push informaldev/ibc-1:$GAIA_BRANCH

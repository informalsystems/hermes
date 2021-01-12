#!/usr/bin/env bash

## Programmatic list for creating Gaia Hub chains for testing IBC.
## Instead of blindly running this code, read it line by line and understand the dependecies and tasks.
## Prerequisites: Log into Docker Hub
set -eou pipefail
GAIA_BRANCH="v3.0.0" # Requires a version with the `--keyring-backend` option. v2.1 and above.

ONE_CHAIN="$(dirname "$0")/../one-chain"
echo $ONE_CHAIN

echo "*** Building config folders"
MONIKER=node_ibc0 \
CHAIN_0_ID=ibc0 \
CHAIN_IP=172.25.0.10 \
CHAIN_HOME=./chains/gaia/$GAIA_BRANCH/ibc0 \
CHAIN_0_RPC_PORT=26657 \
GRPC_PORT=9090 \
CHAIN_0_SAMOLEANS=100000000000
#./bootstrap_gaia.sh
"$ONE_CHAIN" gaiad "$CHAIN_0_ID" ./data $CHAIN_0_RPC_PORT 26656 6060 9090 $CHAIN_0_SAMOLEANS

exit 1

MONIKER=node_ibc1 \
CHAIN_ID=ibc1 \
CHAIN_IP=172.25.0.11 \
CHAIN_HOME=./chains/gaia/$GAIA_BRANCH/ibc1 \
RPC_PORT=26557 \
GRPC_PORT=9091 \
./bootstrap_gaia.sh

echo "*** Requirements"
which docker

echo "*** Create Docker image and upload to Docker Hub"
docker build --build-arg CHAIN=gaia --build-arg RELEASE=$GAIA_BRANCH --build-arg NAME=ibc0 -f --no-cache -t informaldev/ibc0:$GAIA_BRANCH -f gaia.Dockerfile .
docker build --build-arg CHAIN=gaia --build-arg RELEASE=$GAIA_BRANCH --build-arg NAME=ibc1 -f --no-cache -t informaldev/ibc1:$GAIA_BRANCH -f gaia.Dockerfile .

read -p "Press ENTER to push image to Docker Hub or CTRL-C to cancel. " dontcare
docker push informaldev/ibc0:$GAIA_BRANCH
docker push informaldev/ibc1:$GAIA_BRANCH

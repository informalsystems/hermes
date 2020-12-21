#!/usr/bin/env bash

## Programmatic list for creating Gaia Hub chains for testing IBC.
## Instead of blindly running this code, read it line by line and understand the dependecies and tasks.
## Prerequisites: Log into Docker Hub
set -eou pipefail
GAIA_BRANCH="stargate-4" # Requires a version with the `--keyring-backend` option. v2.1 and above.

echo "*** Requirements"
which docker

echo "*** Create Docker image and upload to Docker Hub"
docker build --build-arg CHAIN=gaia --build-arg RELEASE=$GAIA_BRANCH --build-arg NAME=ibc0 -f --no-cache -t informaldev/ibc0:$GAIA_BRANCH -f gaia.Dockerfile .
docker build --build-arg CHAIN=gaia --build-arg RELEASE=$GAIA_BRANCH --build-arg NAME=ibc1 -f --no-cache -t informaldev/ibc1:$GAIA_BRANCH -f gaia.Dockerfile .

read -p "Press ENTER to push image to Docker Hub or CTRL-C to cancel. " dontcare
docker push informaldev/ibc0
docker push informaldev/ibc1

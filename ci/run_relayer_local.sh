#!/usr/bin/env bash

set -eou pipefail

mkdir -p data

echo "*** Run relayer local"
GAIA_RELEASE=stargate-6 \
CHAIN_A=ibc0 \
CHAIN_A_IP=172.25.0.10 \
CHAIN_A_HOME=./data/ibc0 \
CHAIN_A_PORT=26657 \
CHAIN_B=ibc1 \
CHAIN_B_IP=172.25.0.11 \
CHAIN_B_HOME=./data/ibc1 \
CHAIN_B_PORT=26557 \
CONFIG=simple_config.toml \
RELAYER_DIR=. \
./setup_relayer.sh
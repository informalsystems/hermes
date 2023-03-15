#!/usr/bin/env bash

set -euo pipefail

# --- Variables ---

HERMES="cargo run -q --"

# IBC_0_RPC_PORT=26657
IBC_1_RPC_PORT=26557
IBC_1_COMMIT_FILE="data/ibc-1-commit.json"

# --- Helpers ---

warn() {
    echo "WARNING: $*"
}

info() {
    echo "❯ $*"
}

# --- Checks ---

if [ -z "$(which gaiad)" ]; then
    warn "Cannot find 'gaiad', please ensure it is in your \$PATH"
    exit 1
fi
if [ -z "$(which stoml)" ]; then
    warn "Missing stoml utility, install it from https://github.com/freshautomations/stoml/releases"
    exit 1
fi
if [ -z "$(which sconfig)" ]; then
    warn "Missing sconfig utility, install it from https://github.com/freshautomations/sconfig/releases"
    exit 1
fi

# --- Main ---

info "Fetching the latest block height and hash from ibc-1..."
curl -s "localhost:$IBC_1_RPC_PORT/commit" | \
    jq "{height: .result.signed_header.header.height, hash: .result.signed_header.commit.block_id.hash}" | \
    tee "$IBC_1_COMMIT_FILE"

info "Creating new channel between ibc-0 and ibc-1..."
$HERMES --config config.toml create channel --a-chain ibc-0 --b-chain ibc-1 --a-port transfer --b-port transfer --new-client-connection --yes

info "Killing ibc-1..."
pkill -f ibc-1

info "Waiting for ibc-1 to stop..."
sleep 5

info "Creating ibc-1 fork..."
cp -r data/ibc-1 data/ibc-1-f
sconfig data/ibc-1-f/config/config.toml "rpc.laddr=tcp://0.0.0.0:26457"
sconfig data/ibc-1-f/config/config.toml "p2p.laddr=tcp://0.0.0.0:26456"

info "Starting ibc-1..."
gaiad --home ./data/ibc-1 start --pruning=nothing --grpc.address=0.0.0.0:9091 --log_level error > data/ibc-1.log 2>&1 &

info "Starting ibc-1 fork..."
gaiad --home ./data/ibc-1-f start --pruning=nothing --grpc.address=0.0.0.0:9092 --log_level error > data/ibc-1-f.log 2>&1 &

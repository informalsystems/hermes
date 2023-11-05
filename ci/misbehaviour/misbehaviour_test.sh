#!/usr/bin/env bash

set -euo pipefail

# --- Variables ---

HERMES="cargo run --bin hermes -q --"
HERMES_LOG="hermes.log"
DEV_ENV="../../scripts/dev-env"

IBC_1_RPC_PORT=26557

# --- Helpers ---

warn() {
    echo "WARNING: $*"
}

info() {
    echo "❯ $*"
}

# --- Main ---

info "Starting chains"
"$DEV_ENV" config.toml ibc-0 ibc-1 --non-interactive

info "Waiting for the chains to produce a few blocks..."
sleep 10

info "Creating forked chain ibc-1-f"
bash ./create_fork.sh

info "Starting Hermes for ibc-0 and ibc-1"
$HERMES --config config.toml start > "$HERMES_LOG" 2>&1 &
HERMES_PID=$!

info "Waiting for Hermes to start"
sleep 10

info "Update client on ibc-0 against the forked chain ibc-1-f"
$HERMES --config config_fork.toml update client --client 07-tendermint-0 --host-chain ibc-0

info "Wait for chain ibc-1 to stop..."
sleep 10

info "Killing Hermes"
kill -9 "$HERMES_PID"

echo ""
info "--------------------------------------------------"
info "Hermes log:"
info "--------------------------------------------------"
cat "$HERMES_LOG"
info "--------------------------------------------------"
echo ""

if grep -q "Evidence successfully submitted" "$HERMES_LOG"; then
    warn "Misbehaviour detection failed!"
    exit 1
else
    info "Misbehaviour detected and submitted successfully!"
fi

STOPPED_HEIGHT="$(curl -s http://localhost:$IBC_1_RPC_PORT/status | jq -r .result.sync_info.latest_block_height)"

info "Chain ibc-1 stopped at height $STOPPED_HEIGHT"

info "Fetch evidence from block $STOPPED_HEIGHT on ibc-1"
EVIDENCE="$(curl -s "http://localhost:$IBC_1_RPC_PORT/block?height=$STOPPED_HEIGHT" | jq .result.block.evidence)"

info "Found evidence at height $STOPPED_HEIGHT: $EVIDENCE"

if [ "$EVIDENCE" = "null" ]; then
    warn "No evidence found in the latest block on ibc-1"
    exit 1
fi

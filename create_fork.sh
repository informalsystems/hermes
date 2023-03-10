#!/usr/bin/env bash

set -euo pipefail

IBC_0_RPC_PORT=26657
IBC_1_RPC_PORT=26557
IBC_F_RPC_PORT=26457

HERMES="$HOME/.cargo/target/debug/hermes"

echo "❯ Fetching the latest block height and hash from ibc-0..."
curl -s "localhost:$IBC_0_RPC_PORT/commit" | jq "{height: .result.signed_header.header.height, hash: .result.signed_header.commit.block_id.hash}"

echo "❯ Creating new channel between ibc-0 and ibc-1..."
$HERMES --config config.toml create channel --a-chain ibc-0 --b-chain ibc-1 --a-port transfer --b-port transfer --new-client-connection --yes

echo "❯ Killing ibc-1... (waiting 5 seconds)"
pkill -f ibc-1

sleep 5

echo "❯ Creating ibc-1 fork..."
cp -r data/ibc-1 data/ibc-1-f
sconfig data/ibc-1-f/config/config.toml "rpc.laddr=tcp://0.0.0.0:26457"
sconfig data/ibc-1-f/config/config.toml "p2p.laddr=tcp://0.0.0.0:26456"

# echo "❯ Creating Hermes configuration for ibc-1 fork..."
# cp config.toml config_fork.toml
# sconfig config_fork.toml "chains.ibc-1.rpc_addr = \"http://localhost:$IBC_F_RPC_PORT\""

echo "❯ Starting ibc-1..."
gaiad --home ./data/ibc-1 start --pruning=nothing --grpc.address=0.0.0.0:9091 --log_level error > data/ibc-1.log 2>&1 &

echo "❯ Starting ibc-1 fork..."
gaiad --home ./data/ibc-1-f start --pruning=nothing --grpc.address=0.0.0.0:9092 --log_level error > data/ibc-1-f.log 2>&1 &


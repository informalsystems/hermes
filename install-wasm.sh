#!/usr/bin/env bash

CHAIN_ID="ibc0-wasm"
CHAIN_HOME="$HOME/.gm/$CHAIN_ID"
NODE="tcp://localhost:27000"
CONTRACT="./ibc_client_tendermint_cw.wasm"
SIGNER="cosmos15culynpgfdcfupl3f2yrzmav4t8hhpfalc2eu6"
PROPOSAL_ID="1"

# set -e
# set -x
# set -o pipefail

simd tx ibc-wasm store-code "$CONTRACT" \
  --title tmp \
  --summary tmp \
  --fees 1000016stake \
  --deposit 200000stake \
  --home "$CHAIN_HOME" \
  --node "$NODE" \
  --from "$SIGNER" \
  --chain-id "$CHAIN_ID" \
  --keyring-backend test \
  --gas auto \
  -y

MAX_TRIES=10
TRIES=0

while [ $TRIES -lt $MAX_TRIES ]; do
    output=$(simd query gov proposal "$PROPOSAL_ID" --home "$CHAIN_HOME" --node "$NODE" --output json)

    proposal_status=$(echo "$output" | grep -o '"status":"[^"]*' | awk -F ':"' '{print $2}')
    if [ "$proposal_status" == "PROPOSAL_STATUS_DEPOSIT_PERIOD" ]; then
        echo "Proposal status is now $proposal_status. Exiting loop."
        break
    else
        echo "Proposal status is $proposal_status. Continuing to check..."
    fi
    TRIES=$((TRIES + 1))

    sleep 2
done

if [ $TRIES -eq $MAX_TRIES ]; then
    echo "[ERROR] Failed due to an issue with the proposal"
    echo "This is likely due to a misconfiguration in the test script."
    exit 1
fi

simd tx gov deposit "$PROPOSAL_ID" 100000000stake \
  --home "$CHAIN_HOME" \
  --node "$NODE" \
  --from "$SIGNER" \
  --chain-id "$CHAIN_ID" \
  --keyring-backend test \
  --gas auto \
  -y

MAX_TRIES=10
TRIES=0

while [ $TRIES -lt $MAX_TRIES ]; do
    output=$(simd query gov proposal "$PROPOSAL_ID" --home "$CHAIN_HOME" --node "$NODE" --output json)

    proposal_status=$(echo "$output" | grep -o '"status":"[^"]*' | awk -F ':"' '{print $2}')
    if [ "$proposal_status" == "PROPOSAL_STATUS_VOTING_PERIOD" ]; then
        echo "Proposal status is now $proposal_status. Exiting loop."
        break
    else
        echo "Proposal status is $proposal_status. Continuing to check..."
    fi
    TRIES=$((TRIES + 1))

    sleep 2
done

if [ $TRIES -eq $MAX_TRIES ]; then
    echo "[ERROR] Failed due to an issue with the proposal"
    echo "This is likely due to a misconfiguration in the test script."
    exit 1
fi

simd tx gov vote "$PROPOSAL_ID" yes \
  --home "$CHAIN_HOME" \
  --node "$NODE" \
  --from "$SIGNER" \
  --chain-id "$CHAIN_ID" \
  --keyring-backend test \
  --gas auto \
  -y

MAX_TRIES=10
TRIES=0

while [ $TRIES -lt $MAX_TRIES ]; do
    output=$(simd query gov proposal "$PROPOSAL_ID" --home "$CHAIN_HOME" --node "$NODE" --output json)

    proposal_status=$(echo "$output" | grep -o '"status":"[^"]*' | awk -F ':"' '{print $2}')
    if [ "$proposal_status" == "PROPOSAL_STATUS_PASSED" ]; then
        echo "Proposal status is now $proposal_status. Exiting loop."
        break
    else
        echo "Proposal status is $proposal_status. Continuing to check..."
    fi
    TRIES=$((TRIES + 1))

    sleep 2
done

if [ $TRIES -eq $MAX_TRIES ]; then
    echo "[ERROR] Failed due to an issue with the proposal"
    echo "This is likely due to a misconfiguration in the test script."
    exit 1
fi

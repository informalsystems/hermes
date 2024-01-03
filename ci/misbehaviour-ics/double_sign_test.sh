#!/bin/bash
# shellcheck disable=2086,2004

set -eu

DEBUG=${DEBUG:-false}

if [ "$DEBUG" = true ]; then
    set -x
fi

# User balance of stake tokens 
USER_COINS="100000000000stake"
# Amount of stake tokens staked
STAKE="100000000stake"
# Node IP address
NODE_IP="127.0.0.1"

# Home directory
HOME_DIR="/tmp/hermes-ics-double-sign"

# Hermes debug
if [ "$DEBUG" = true ]; then
    HERMES_DEBUG="--debug=rpc"
else
    HERMES_DEBUG=""
fi
# Hermes config
HERMES_CONFIG="$HOME_DIR/hermes.toml"
# Hermes binary
HERMES_BIN="cargo run -q --bin hermes -- $HERMES_DEBUG --config $HERMES_CONFIG"

# Validator moniker
MONIKERS=("coordinator" "alice" "bob")
LEAD_VALIDATOR_MONIKER="coordinator"

# Hermes will connect to this node on both provider and consumer
HERMES_VALIDATOR_MONIKER="bob"

PROV_NODES_ROOT_DIR=${HOME_DIR}/nodes/provider
CONS_NODES_ROOT_DIR=${HOME_DIR}/nodes/consumer

# Base port. Ports assigned after these ports sequentially by nodes.
RPC_LADDR_BASEPORT=29170
P2P_LADDR_BASEPORT=29180
GRPC_LADDR_BASEPORT=29190
NODE_ADDRESS_BASEPORT=29200
PPROF_LADDR_BASEPORT=29210
CLIENT_BASEPORT=29220


# Clean start
pkill -f interchain-security-pd &> /dev/null || true
pkill -f interchain-security-cd &> /dev/null || true
pkill -f hermes &> /dev/null || true
sleep 1

mkdir -p "${HOME_DIR}"
rm -rf "${PROV_NODES_ROOT_DIR}"
rm -rf "${CONS_NODES_ROOT_DIR}"

# Let lead validator create genesis file
LEAD_VALIDATOR_PROV_DIR=${PROV_NODES_ROOT_DIR}/provider-${LEAD_VALIDATOR_MONIKER}
LEAD_VALIDATOR_CONS_DIR=${CONS_NODES_ROOT_DIR}/consumer-${LEAD_VALIDATOR_MONIKER}
LEAD_PROV_KEY=${LEAD_VALIDATOR_MONIKER}-key
LEAD_PROV_LISTEN_ADDR=tcp://${NODE_IP}:${RPC_LADDR_BASEPORT}

for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}
    # validator key
    PROV_KEY=${MONIKER}-key
    PROV_KEY2=${MONIKER}-key2

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # Build genesis file and node directory structure
    interchain-security-pd init $MONIKER --chain-id provider --home ${PROV_NODE_DIR}
    jq ".app_state.gov.params.voting_period = \"5s\" | .app_state.staking.params.unbonding_time = \"86400s\"" \
    ${PROV_NODE_DIR}/config/genesis.json > \
    ${PROV_NODE_DIR}/edited_genesis.json && mv ${PROV_NODE_DIR}/edited_genesis.json ${PROV_NODE_DIR}/config/genesis.json


    sleep 1

    # Create account keypair
    interchain-security-pd keys add $PROV_KEY  --home ${PROV_NODE_DIR} --keyring-backend test --output json > ${PROV_NODE_DIR}/${PROV_KEY}.json  2>&1
    interchain-security-pd keys add $PROV_KEY2 --home ${PROV_NODE_DIR} --keyring-backend test --output json > ${PROV_NODE_DIR}/${PROV_KEY2}.json 2>&1
    sleep 1

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json ${PROV_NODE_DIR}/config/genesis.json
    fi

    # Add stake to user
    PROV_ACCOUNT_ADDR=$(jq -r '.address' ${PROV_NODE_DIR}/${PROV_KEY}.json)
    interchain-security-pd genesis add-genesis-account $PROV_ACCOUNT_ADDR $USER_COINS --home ${PROV_NODE_DIR} --keyring-backend test

    PROV_ACCOUNT_ADDR2=$(jq -r '.address' ${PROV_NODE_DIR}/${PROV_KEY2}.json)
    interchain-security-pd genesis add-genesis-account $PROV_ACCOUNT_ADDR2 $USER_COINS --home ${PROV_NODE_DIR} --keyring-backend test
    sleep 1

    # copy genesis out, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${PROV_NODE_DIR}/config/genesis.json ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json
    fi

    PPROF_LADDR=${NODE_IP}:$(($PPROF_LADDR_BASEPORT + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + $index))

    # adjust configs of this node
    sed -i -r 's/timeout_commit = "5s"/timeout_commit = "3s"/g' ${PROV_NODE_DIR}/config/config.toml
    sed -i -r 's/timeout_propose = "3s"/timeout_propose = "1s"/g' ${PROV_NODE_DIR}/config/config.toml

    # make address book non-strict. necessary for this setup
    sed -i -r 's/addr_book_strict = true/addr_book_strict = false/g' ${PROV_NODE_DIR}/config/config.toml

    # avoid port double binding
    sed -i -r  "s/pprof_laddr = \"localhost:6060\"/pprof_laddr = \"${PPROF_LADDR}\"/g" ${PROV_NODE_DIR}/config/config.toml

    # allow duplicate IP addresses (all nodes are on the same machine)
    sed -i -r  's/allow_duplicate_ip = false/allow_duplicate_ip = true/g' ${PROV_NODE_DIR}/config/config.toml
done

for MONIKER in "${MONIKERS[@]}"
do
    # validator key
    PROV_KEY=${MONIKER}-key

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json* ${PROV_NODE_DIR}/config/genesis.json
    fi

    # Stake 1/1000 user's coins
    interchain-security-pd genesis gentx $PROV_KEY  $STAKE --chain-id provider --home ${PROV_NODE_DIR} --keyring-backend test --moniker $MONIKER
    sleep 1

    # Copy gentxs to the lead validator for possible future collection. 
    # Obviously we don't need to copy the first validator's gentx to itself
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${PROV_NODE_DIR}/config/gentx/* ${LEAD_VALIDATOR_PROV_DIR}/config/gentx/
    fi
done

# Collect genesis transactions with lead validator
interchain-security-pd genesis collect-gentxs --home ${LEAD_VALIDATOR_PROV_DIR} --gentx-dir ${LEAD_VALIDATOR_PROV_DIR}/config/gentx/

sleep 1


for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}

    PERSISTENT_PEERS=""

    for peer_index in "${!MONIKERS[@]}"
    do
        if [ $index == $peer_index ]; then
            continue
        fi
        PEER_MONIKER=${MONIKERS[$peer_index]}

        PEER_PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${PEER_MONIKER}

        PEER_NODE_ID=$(interchain-security-pd tendermint show-node-id --home ${PEER_PROV_NODE_DIR})

        PEER_P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + $peer_index))
        PERSISTENT_PEERS="$PERSISTENT_PEERS,$PEER_NODE_ID@${NODE_IP}:${PEER_P2P_LADDR_PORT}"
    done

    # remove trailing comma from persistent peers
    PERSISTENT_PEERS=${PERSISTENT_PEERS:1}

    # validator key
    PROV_KEY=${MONIKER}-key
    PROV_KEY2=${MONIKER}-key2

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${PROV_NODES_ROOT_DIR}/consumer-${MONIKER}

    # copy genesis in, unless this validator is already the lead validator and thus it already has its genesis
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json ${PROV_NODE_DIR}/config/genesis.json
    fi

    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + $index))
    GRPC_LADDR_PORT=$(($GRPC_LADDR_BASEPORT + $index))
    NODE_ADDRESS_PORT=$(($NODE_ADDRESS_BASEPORT + $index))

    if [ $MONIKER == $HERMES_VALIDATOR_MONIKER ]; then
        PRPC_LADDR_PORT=$RPC_LADDR_PORT
        PGRPC_LADDR_PORT=$GRPC_LADDR_PORT
    fi
    # Start gaia
    interchain-security-pd start \
        --home ${PROV_NODE_DIR} \
        --p2p.persistent_peers ${PERSISTENT_PEERS} \
        --rpc.laddr tcp://${NODE_IP}:${RPC_LADDR_PORT} \
        --grpc.address ${NODE_IP}:${GRPC_LADDR_PORT} \
        --address tcp://${NODE_IP}:${NODE_ADDRESS_PORT} \
        --p2p.laddr tcp://${NODE_IP}:${P2P_LADDR_PORT} \
        --grpc-web.enable=false &> ${PROV_NODE_DIR}/logs &

    sleep 5
done

# Build consumer chain proposal file
tee ${LEAD_VALIDATOR_PROV_DIR}/consumer-proposal.json<<EOF
{
    "title": "Create a chain",
    "summary": "Gonna be a great chain",
    "chain_id": "consumer",
    "initial_height": {
        "revision_height": 1
    },
    "genesis_hash": "Z2VuX2hhc2g=",
    "binary_hash": "YmluX2hhc2g=",
    "spawn_time": "2023-03-11T09:02:14.718477-08:00",
    "deposit": "10000001stake",
    "consumer_redistribution_fraction": "0.75",
    "blocks_per_distribution_transmission": 1000,
    "historical_entries": 10000,
    "unbonding_period": 864000000000000,
    "ccv_timeout_period": 259200000000000,
    "transfer_timeout_period": 1800000000000
}
EOF

sleep 5
interchain-security-pd keys show $LEAD_PROV_KEY --keyring-backend test --home ${LEAD_VALIDATOR_PROV_DIR}

# Submit consumer chain proposal
interchain-security-pd tx gov submit-legacy-proposal consumer-addition ${LEAD_VALIDATOR_PROV_DIR}/consumer-proposal.json --chain-id provider --from $LEAD_PROV_KEY --home ${LEAD_VALIDATOR_PROV_DIR} --node $LEAD_PROV_LISTEN_ADDR  --keyring-backend test -y --gas auto

sleep 3

# Vote yes to proposal
for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}
    PROV_KEY=${MONIKER}-key
    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))
    RPC_LADDR=tcp://${NODE_IP}:${RPC_LADDR_PORT}

    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}
    interchain-security-pd tx gov vote 1 yes --from $PROV_KEY --chain-id provider --home ${PROV_NODE_DIR} --node $RPC_LADDR -y --keyring-backend test
done

HERMES_PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${HERMES_VALIDATOR_MONIKER}
HERMES_KEY=${HERMES_VALIDATOR_MONIKER}-key
HERMES_KEY2=${HERMES_VALIDATOR_MONIKER}-key2
HERMES_CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${HERMES_VALIDATOR_MONIKER}

# # ## CONSUMER CHAIN ##

### Assert that the proposal for the consumer chain passed
PROPOSAL_STATUS_PASSED="PROPOSAL_STATUS_PASSED"
MAX_TRIES=10
TRIES=0

cat ${PROV_NODE_DIR}/config/genesis.json | grep "period"

while [ $TRIES -lt $MAX_TRIES ]; do
    output=$(interchain-security-pd query gov proposal 1 --home ${LEAD_VALIDATOR_PROV_DIR} --node $LEAD_PROV_LISTEN_ADDR --output json)

    proposal_status=$(echo "$output" | grep -o '"status":"[^"]*' | awk -F ':"' '{print $2}')
    if [ "$proposal_status" = "$PROPOSAL_STATUS_PASSED" ]; then
        echo "Proposal status is now $proposal_status. Exiting loop."
        break
    else
        echo "Proposal status is $proposal_status. Continuing to check..."
    fi
    TRIES=$((TRIES + 1))

    sleep 2
done

if [ $TRIES -eq $MAX_TRIES ]; then
    echo "[ERROR] Failed due to an issue with the consumer proposal"
    echo "This is likely due to a misconfiguration in the test script."
    exit 0
fi

# # Clean start
for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}
    # validator key
    PROV_KEY=${MONIKER}-key
    PROV_KEY2=${MONIKER}-key2

    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # Build genesis file and node directory structure
    interchain-security-cd init $MONIKER --chain-id consumer  --home ${CONS_NODE_DIR}

    sleep 1

    # Create account keypair
    interchain-security-cd keys add $PROV_KEY  --home ${CONS_NODE_DIR} --keyring-backend test --output json > ${CONS_NODE_DIR}/${PROV_KEY}.json  2>&1
    interchain-security-cd keys add $PROV_KEY2 --home ${CONS_NODE_DIR} --keyring-backend test --output json > ${CONS_NODE_DIR}/${PROV_KEY2}.json 2>&1
    sleep 1

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json ${CONS_NODE_DIR}/config/genesis.json
    fi

    # Add stake to user
    CONS_ACCOUNT_ADDR=$(jq -r '.address' ${CONS_NODE_DIR}/${PROV_KEY}.json)
    interchain-security-cd genesis add-genesis-account $CONS_ACCOUNT_ADDR $USER_COINS --home ${CONS_NODE_DIR}
    CONS_ACCOUNT_ADDR2=$(jq -r '.address' ${CONS_NODE_DIR}/${PROV_KEY2}.json)
    interchain-security-cd genesis add-genesis-account $CONS_ACCOUNT_ADDR2 $USER_COINS --home ${CONS_NODE_DIR}
    sleep 10

    ### this probably does not have to be done for each node
    # Add consumer genesis states to genesis file
    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))
    RPC_LADDR=tcp://${NODE_IP}:${RPC_LADDR_PORT}
    interchain-security-pd query provider consumer-genesis consumer --home ${PROV_NODE_DIR} --node ${RPC_LADDR} -o json > consumer_gen.json
    jq -s '.[0].app_state.ccvconsumer = .[1] | .[0]' ${CONS_NODE_DIR}/config/genesis.json consumer_gen.json > ${CONS_NODE_DIR}/edited_genesis.json \
    && mv ${CONS_NODE_DIR}/edited_genesis.json ${CONS_NODE_DIR}/config/genesis.json
    rm consumer_gen.json
    ###

    # copy genesis out, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${CONS_NODE_DIR}/config/genesis.json ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json
    fi

    PPROF_LADDR=${NODE_IP}:$(($PPROF_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))

    # adjust configs of this node
    sed -i -r 's/timeout_commit = "5s"/timeout_commit = "3s"/g' ${CONS_NODE_DIR}/config/config.toml
    sed -i -r 's/timeout_propose = "3s"/timeout_propose = "1s"/g' ${CONS_NODE_DIR}/config/config.toml

    # make address book non-strict. necessary for this setup
    sed -i -r 's/addr_book_strict = true/addr_book_strict = false/g' ${CONS_NODE_DIR}/config/config.toml

    # avoid port double binding
    sed -i -r  "s/pprof_laddr = \"localhost:6060\"/pprof_laddr = \"${PPROF_LADDR}\"/g" ${CONS_NODE_DIR}/config/config.toml

    # allow duplicate IP addresses (all nodes are on the same machine)
    sed -i -r  's/allow_duplicate_ip = false/allow_duplicate_ip = true/g' ${CONS_NODE_DIR}/config/config.toml

    # Create validator states
    echo '{"height": "0","round": 0,"step": 0}' > ${CONS_NODE_DIR}/data/priv_validator_state.json

    # Copy validator key files
    cp ${PROV_NODE_DIR}/config/priv_validator_key.json ${CONS_NODE_DIR}/config/priv_validator_key.json
    cp ${PROV_NODE_DIR}/config/node_key.json ${CONS_NODE_DIR}/config/node_key.json

    # Set default client port
    CLIENT_PORT=$(($CLIENT_BASEPORT + ${#MONIKERS[@]} + $index))
    sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${NODE_IP}:${CLIENT_PORT}\"/" ${CONS_NODE_DIR}/config/client.toml

done

sleep 1


for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}

    PERSISTENT_PEERS=""

    for peer_index in "${!MONIKERS[@]}"
    do
        if [ $index == $peer_index ]; then
            continue
        fi
        PEER_MONIKER=${MONIKERS[$peer_index]}

        PEER_CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${PEER_MONIKER}

        PEER_NODE_ID=$(interchain-security-pd tendermint show-node-id --home ${PEER_CONS_NODE_DIR})

        PEER_P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + ${#MONIKERS[@]} + $peer_index))
        PERSISTENT_PEERS="$PERSISTENT_PEERS,$PEER_NODE_ID@${NODE_IP}:${PEER_P2P_LADDR_PORT}"
    done

    # remove trailing comma from persistent peers
    PERSISTENT_PEERS=${PERSISTENT_PEERS:1}

    # validator key
    PROV_KEY=${MONIKER}-key

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # copy genesis in, unless this validator is already the lead validator and thus it already has its genesis
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json ${CONS_NODE_DIR}/config/genesis.json
    fi

    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    P2P_LADDR_PORT=$(($P2P_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    GRPC_LADDR_PORT=$(($GRPC_LADDR_BASEPORT + ${#MONIKERS[@]} + $index))
    NODE_ADDRESS_PORT=$(($NODE_ADDRESS_BASEPORT + ${#MONIKERS[@]} + $index))

    if [ $MONIKER == $HERMES_VALIDATOR_MONIKER ]; then
        CRPC_LADDR_PORT=$RPC_LADDR_PORT
        CGRPC_LADDR_PORT=$GRPC_LADDR_PORT
    fi
    # Start gaia
    interchain-security-cd start \
        --home ${CONS_NODE_DIR} \
        --p2p.persistent_peers ${PERSISTENT_PEERS} \
        --rpc.laddr tcp://${NODE_IP}:${RPC_LADDR_PORT} \
        --grpc.address ${NODE_IP}:${GRPC_LADDR_PORT} \
        --address tcp://${NODE_IP}:${NODE_ADDRESS_PORT} \
        --p2p.laddr tcp://${NODE_IP}:${P2P_LADDR_PORT} \
        --grpc-web.enable=false &> ${CONS_NODE_DIR}/logs &

    sleep 6
done

## Cause double signing

# create directory for double signing node
mkdir $CONS_NODES_ROOT_DIR/consumer-bob-sybil/
cp -r $CONS_NODES_ROOT_DIR/consumer-bob/* $CONS_NODES_ROOT_DIR/consumer-bob-sybil

# clear state in consumer-bob-sybil
echo '{"height": "0","round": 0,"step": 0,"signature":"","signbytes":""}' > $CONS_NODES_ROOT_DIR/consumer-bob-sybil/data/priv_validator_state.json

# add new node key to sybil
# key was generated using gaiad init
# if the node key is not unique, double signing cannot be achieved
# and errors such as this can be seen in the terminal
# 5:54PM ERR found conflicting vote from ourselves; did you unsafe_reset a validator? height=1961 module=consensus round=0 type=2
# 5:54PM ERR failed to process message err="conflicting votes from validator C888306A908A217B9A943D1DAD8790044D0947A4"
echo '{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"tj55by/yYwruSz4NxsOG9y9k2WrPvKLXKQdz/9jL9Uptmi647OYpcisjwf92TyA+wCUYVDOgW7D53Q+638l9/w=="}}' > $CONS_NODES_ROOT_DIR/consumer-bob-sybil/config/node_key.json

# does not use persistent peers; will do a lookup in genesis.json to find peers
#ARGS="--address tcp://$CHAIN_PREFIX.252:26655 --rpc.laddr tcp://$CHAIN_PREFIX.252:26658 --grpc.address $CHAIN_PREFIX.252:9091 --log_level trace --p2p.laddr tcp://$CHAIN_PREFIX.252:26656 --grpc-web.enable=false"

# start double signing node - it should not talk to the node with the same key
#ip netns exec $HOME/nodes/consumer/consumer-bob-sybil $BIN $ARGS --home $HOME/nodes/consumer/consumer-bob-sybil  start &> $HOME/nodes/consumer/consumer-bob-sybil/logs &

# Start gaia
interchain-security-cd start \
    --home $CONS_NODES_ROOT_DIR/consumer-bob-sybil \
    --p2p.persistent_peers ${PERSISTENT_PEERS} \
    --rpc.laddr tcp://${NODE_IP}:29179 \
    --grpc.address ${NODE_IP}:29199 \
    --address tcp://${NODE_IP}:29209 \
    --p2p.laddr tcp://${NODE_IP}:29189 \
    --grpc-web.enable=false &> $CONS_NODES_ROOT_DIR/consumer-bob-sybil/logs &

# Setup Hermes config file

tee $HERMES_CONFIG<<EOF
[global]
log_level = "debug"

[mode]

[mode.clients]
enabled = true
refresh = true
misbehaviour = true

[mode.connections]
enabled = false

[mode.channels]
enabled = false

[mode.packets]
enabled = true

[[chains]]
id = "consumer"
type = "CosmosSdk"
rpc_addr = "http://${NODE_IP}:${CRPC_LADDR_PORT}"
event_source = { mode = 'push', url = 'ws://${NODE_IP}:${CRPC_LADDR_PORT}/websocket' , batch_delay = '50ms' }
grpc_addr = "tcp://${NODE_IP}:${CGRPC_LADDR_PORT}"
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
key_name = "relayer"
max_gas = 2000000
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "1days"
ccv_consumer_chain = true

[chains.gas_price]
      denom = "stake"
      price = 0.00

[chains.trust_threshold]
      denominator = "3"
      numerator = "1"

[[chains]]
id = "provider"
type = "CosmosSdk"
rpc_addr = "http://${NODE_IP}:${PRPC_LADDR_PORT}"
event_source = { mode = 'push', url = 'ws://${NODE_IP}:${PRPC_LADDR_PORT}/websocket' , batch_delay = '50ms' }
grpc_addr = "tcp://${NODE_IP}:${PGRPC_LADDR_PORT}"
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
key_name = "relayer"
max_gas = 2000000
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "1days"

[chains.gas_price]
      denom = "stake"
      price = 0.00

[chains.trust_threshold]
      denominator = "3"
      numerator = "1"
EOF

# Delete all previous keys in relayer
$HERMES_BIN keys delete --chain consumer --all
$HERMES_BIN keys delete --chain provider --all

# Restore keys to hermes relayer
$HERMES_BIN keys add --key-name relayer  --key-file ${HERMES_PROV_NODE_DIR}/${HERMES_KEY}.json  --chain provider
$HERMES_BIN keys add --key-name evidence --key-file ${HERMES_PROV_NODE_DIR}/${HERMES_KEY2}.json --chain provider
$HERMES_BIN keys add --key-name relayer  --key-file ${HERMES_CONS_NODE_DIR}/${HERMES_KEY}.json  --chain consumer
$HERMES_BIN keys add --key-name evidence --key-file ${HERMES_CONS_NODE_DIR}/${HERMES_KEY2}.json --chain consumer

# CCV connection and channel
$HERMES_BIN create connection \
    --a-chain consumer \
    --a-client 07-tendermint-0 \
    --b-client 07-tendermint-0

# Dummy client and connection for the test
$HERMES_BIN create client \
    --host-chain provider \
    --reference-chain consumer \
    --trusting-period 57600s

$HERMES_BIN create client \
    --host-chain consumer \
    --reference-chain provider \
    --trusting-period 57600s

$HERMES_BIN create connection \
    --a-chain consumer \
    --a-client 07-tendermint-1 \
    --b-client 07-tendermint-1

# CCV channel
$HERMES_BIN create channel \
    --a-chain consumer \
    --a-port consumer \
    --b-port provider \
    --order ordered \
    --channel-version 1 \
    --a-connection connection-0

$HERMES_BIN start &> $HOME_DIR/hermes-start-logs.txt &

$HERMES_BIN evidence --chain consumer --key-name evidence &> $HOME_DIR/hermes-evidence-logs.txt &

for _ in $(seq 1 10)
do
    sleep 5

    MSG="successfully submitted double voting evidence to chain"
    
    if grep -c "$MSG" $HOME_DIR/hermes-evidence-logs.txt; then
        echo "[SUCCESS] Successfully submitted double voting evidence to provider chain"
        exit 0
    fi
done

echo "[ERROR] Failed to submit double voting evidence to provider chain"
echo ""
echo "---------------------------------------------------------------"
echo "Hermes start logs:"
cat $HOME_DIR/hermes-start-logs.txt
echo "---------------------------------------------------------------"
echo "Hermes evidence logs:"
cat $HOME_DIR/hermes-evidence-logs.txt
echo "---------------------------------------------------------------"

exit 1


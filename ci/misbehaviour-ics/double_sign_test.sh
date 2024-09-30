#!/bin/bash
# shellcheck disable=2086,2004

## Prerequisites:
#  * ICS v6.x
#  * Hermes v1.10.3+45a29cc00

set -eu

DEBUG=${DEBUG:-false}

if [ "$DEBUG" = true ]; then
    set -x
fi

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

# User balance of stake tokens
USER_COINS="100000000000stake"
# Amount of stake tokens staked
STAKE="100000000stake"
# Node IP address
NODE_IP="127.0.0.1"

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
sleep 1
rm -rf ${PROV_NODES_ROOT_DIR}

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

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # Build genesis file and node directory structure
    interchain-security-pd init $MONIKER --chain-id provider --home ${PROV_NODE_DIR}
    jq ".app_state.gov.params.voting_period = \"10s\" \
    | .app_state.gov.params.expedited_voting_period = \"9s\" \
    | .app_state.staking.params.unbonding_time = \"86400s\" \
    | .app_state.provider.params.blocks_per_epoch = \"5\"" \
    ${PROV_NODE_DIR}/config/genesis.json > \
    ${PROV_NODE_DIR}/edited_genesis.json && mv ${PROV_NODE_DIR}/edited_genesis.json ${PROV_NODE_DIR}/config/genesis.json

    sleep 1

    # Create account keypair
    interchain-security-pd keys add $PROV_KEY --home ${PROV_NODE_DIR} --keyring-backend test --output json > ${PROV_NODE_DIR}/${PROV_KEY}.json 2>&1
    sleep 1

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_PROV_DIR}/config/genesis.json ${PROV_NODE_DIR}/config/genesis.json
    fi

    # Add stake to user
    PROV_ACCOUNT_ADDR=$(jq -r '.address' ${PROV_NODE_DIR}/${PROV_KEY}.json)
    interchain-security-pd genesis add-genesis-account $PROV_ACCOUNT_ADDR $USER_COINS --home ${PROV_NODE_DIR} --keyring-backend test
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
    interchain-security-pd genesis gentx $PROV_KEY $STAKE --chain-id provider --home ${PROV_NODE_DIR} --keyring-backend test --moniker $MONIKER
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
tee ${PROV_NODE_DIR}/create-consumer-msg.json<<EOF
{
	"chain_id" : "consumer",
	"metadata": {
        "name": "consumer-1-metadata-name",
        "description":"consumer-1-metadata-description",
        "metadata": "consumer-1-metadata-metadata"
    }
}
EOF

sleep 5

TX_RES=$(interchain-security-pd tx provider create-consumer \
    ${PROV_NODE_DIR}/create-consumer-msg.json \
    --chain-id provider \
    --from $PROV_KEY \
    --keyring-backend test \
    --home $PROV_NODE_DIR \
    --node tcp://${NODE_IP}:${RPC_LADDR_PORT} \
    -o json -y)

sleep 5

TX_RES=$(interchain-security-pd q tx --type=hash $(echo $TX_RES | jq -r '.txhash') \
    --home ${PROV_NODE_DIR} \
    --node tcp://${NODE_IP}:${RPC_LADDR_PORT} \
    -o json)


echo $TX_RES | jq .code

if [ "$(echo $TX_RES | jq -r .code )" != "0" ]; then
  echo consumer creation failed with code: $(echo $TX_RES | jq .code )
  exit 1
fi


EVENTS=$(echo $TX_RES | jq -c '.events[]')
found=false
CONSUMER_ID=""
for event in $EVENTS; do
    type=$(echo "$event" | jq -r '.type')
    echo $type
    if [ "$type" = "create_consumer" ]; then
       attrs=$(echo $event | jq -c '.attributes[]')
       for attr in $attrs; do
            key=$(echo "$attr" | jq -r '.key')
            if [ "$key" = "consumer_id" ]; then
                CONSUMER_ID=$(echo "$attr" | jq -r '.value')
            fi
       done
       found=true
       break
    fi
done

if [ "$found" = false ]; then
    echo "consumer creation event not found"
    exit 1
fi

echo "consumer created: $CONSUMER_ID"


AUTHORITY=cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn
PROV_ACCOUNT_ADDR=$(jq -r '.address' ${PROV_NODE_DIR}/${PROV_KEY}.json)

## Grant the consumer ownership to the Gov module
tee ${PROV_NODE_DIR}/update-consumer-msg.json<<EOF
{
	"consumer_id" : "$CONSUMER_ID",
    "owner_address": "$PROV_ACCOUNT_ADDR",
    "new_owner_address": "$AUTHORITY",
	"metadata": $(jq -r '.metadata' ${PROV_NODE_DIR}/create-consumer-msg.json)
}
EOF

TX_RES=$(interchain-security-pd tx provider update-consumer \
    ${PROV_NODE_DIR}/update-consumer-msg.json \
    --chain-id provider \
    --from $PROV_KEY \
    --keyring-backend test \
    --home $PROV_NODE_DIR \
    --node tcp://${NODE_IP}:${RPC_LADDR_PORT} \
    -o json -y)

sleep 5

## Update consumer to TopN by submitting a gov proposal
tee ${PROV_NODE_DIR}/consumer_prop.json<<EOF
{
    "messages": [
        {
            "@type": "/interchain_security.ccv.provider.v1.MsgUpdateConsumer",
            "consumer_id": "${CONSUMER_ID}",
            "owner": "$AUTHORITY",
            "metadata": $(jq -r '.metadata' ${PROV_NODE_DIR}/create-consumer-msg.json),
            "initialization_parameters": {
                "initial_height": {
                    "revision_number": 0,
                    "revision_height": 1
                },
                "genesis_hash": "2D5C2110941DA54BE07CBB9FACD7E4A2E3253E79BE7BE3E5A1A7BDA518BAA4BE",
                "binary_hash": "2D5C2110941DA54BE07CBB9FACD7E4A2E3253E79BE7BE3E5A1A7BDA518BAA4BE",
                "spawn_time": "2023-03-11T09:02:14.718477-08:00",
                "ccv_timeout_period": "2419200s",
                "unbonding_period": "2419200s",
                "transfer_timeout_period": "3600s",
                "consumer_redistribution_fraction": "0.75",
                "blocks_per_distribution_transmission": 1500,
                "historical_entries": 1000,
                "distribution_transmission_channel": ""
            },
            "power_shaping_parameters": {
                "top_N": 100,
                "validators_power_cap": 0,
                "validator_set_cap": 50,
                "allowlist": [],
                "denylist": [],
                "min_stake": 1000,
                "allow_inactive_vals": true
            }
        }
    ],
    "metadata": "ipfs://CID",
    "deposit": "10000000stake",
    "title": "\"update consumer 0 to top N\"",
    "summary": "\"update consumer 0 to top N\"",
    "expedited": false
}
EOF

PROP_ID=1

interchain-security-pd tx gov submit-proposal ${PROV_NODE_DIR}/consumer_prop.json \
    --chain-id provider \
    --from $PROV_KEY \
    --keyring-backend test \
    --home $PROV_NODE_DIR \
    --node tcp://${NODE_IP}:${RPC_LADDR_PORT} \
    -o json -y

sleep 3

## Vote yes to proposal
for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}

    # validator key
    PROV_KEY=${MONIKER}-key

    # home directory of this validator on provider
    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))

    # Start gaia
    interchain-security-pd tx gov vote $PROP_ID yes \
        --home ${PROV_NODE_DIR} \
        --chain-id provider \
        --from $PROV_KEY \
        --keyring-backend test \
        --node tcp://${NODE_IP}:${RPC_LADDR_PORT} \
        -o json -y

    sleep 1
done

sleep 10

## Note that the validators should validate the consumer once the proposal passes

# # ## CONSUMER CHAIN ##

# # Clean start
pkill -f interchain-security-cd &> /dev/null || true
sleep 1
rm -rf ${CONS_NODES_ROOT_DIR}

for index in "${!MONIKERS[@]}"
do
    MONIKER=${MONIKERS[$index]}
    # validator key
    PROV_KEY=${MONIKER}-key

    PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${MONIKER}

    # home directory of this validator on consumer
    CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}

    # Build genesis file and node directory structure
    interchain-security-cd init $MONIKER --chain-id consumer  --home ${CONS_NODE_DIR}

    sleep 1

    # Create account keypair
    interchain-security-cd keys add $PROV_KEY --home  ${CONS_NODE_DIR} --keyring-backend test --output json > ${CONS_NODE_DIR}/${PROV_KEY}.json 2>&1
    sleep 1

    # copy genesis in, unless this validator is the lead validator
    if [ $MONIKER != $LEAD_VALIDATOR_MONIKER ]; then
        cp ${LEAD_VALIDATOR_CONS_DIR}/config/genesis.json ${CONS_NODE_DIR}/config/genesis.json
    fi

    # Add stake to user
    CONS_ACCOUNT_ADDR=$(jq -r '.address' ${CONS_NODE_DIR}/${PROV_KEY}.json)
    interchain-security-cd genesis add-genesis-account $CONS_ACCOUNT_ADDR $USER_COINS --home ${CONS_NODE_DIR}

    ### this probably doesnt have to be done for each node
    # Add consumer genesis states to genesis file
    RPC_LADDR_PORT=$(($RPC_LADDR_BASEPORT + $index))
    RPC_LADDR=tcp://${NODE_IP}:${RPC_LADDR_PORT}
    interchain-security-pd query provider consumer-genesis $CONSUMER_ID \
        --home ${PROV_NODE_DIR} \
        --node ${RPC_LADDR} -o json > consumer_gen.json

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

## Setup Hermes

HERMES_PROV_NODE_DIR=${PROV_NODES_ROOT_DIR}/provider-${HERMES_VALIDATOR_MONIKER}
HERMES_KEY=${HERMES_VALIDATOR_MONIKER}-key
HERMES_CONS_NODE_DIR=${CONS_NODES_ROOT_DIR}/consumer-${HERMES_VALIDATOR_MONIKER}

tee $HERMES_CONFIG <<EOF
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
        id = "provider"
        account_prefix = "cosmos"
        clock_drift = "5s"
        gas_multiplier = 1.1
        rpc_addr = "http://${NODE_IP}:${PRPC_LADDR_PORT}"
        grpc_addr = "tcp://${NODE_IP}:${PGRPC_LADDR_PORT}"
        key_name = "query"
        max_gas = 20000000
        rpc_timeout = "10s"
        store_prefix = "ibc"
        trusting_period = "14days"
        event_source = { mode = 'pull', interval = '100ms' }
        ccv_consumer_chain = false

        [chains.gas_price]
            denom = "stake"
            price = 0.000

        [chains.trust_threshold]
            denominator = "3"
            numerator = "1"



    [[chains]]
        id = "consumer"
        account_prefix = "consumer"
        clock_drift = "5s"
        gas_multiplier = 1.1
        rpc_addr = "http://${NODE_IP}:${CRPC_LADDR_PORT}"
        grpc_addr = "tcp://${NODE_IP}:${CGRPC_LADDR_PORT}"
        key_name = "query"
        max_gas = 20000000
        rpc_timeout = "10s"
        store_prefix = "ibc"
        trusting_period = "14days"
        event_source = { mode = 'pull', interval = '100ms' }
        ccv_consumer_chain = true

        [chains.gas_price]
            denom = "stake"
            price = 0.000

        [chains.trust_threshold]
            denominator = "3"
            numerator = "1"
EOF

# Delete all previous keys in relayer
$HERMES_BIN keys delete --chain consumer --all
$HERMES_BIN keys delete --chain provider --all

# Restore keys to hermes relayer
$HERMES_BIN keys add --key-file  ${HERMES_PROV_NODE_DIR}/${HERMES_KEY}.json --chain provider
$HERMES_BIN keys add --key-file  ${HERMES_CONS_NODE_DIR}/${HERMES_KEY}.json --chain consumer

sleep 5

$HERMES_BIN create connection \
     --a-chain consumer \
    --a-client 07-tendermint-0 \
    --b-client 07-tendermint-0

$HERMES_BIN create channel \
    --a-chain consumer \
    --a-port consumer \
    --b-port provider \
    --order ordered \
    --channel-version 1 \
    --a-connection connection-0

sleep 5

## Cause double signing

CONS_NODE_SYBIL_DIR=${CONS_NODES_ROOT_DIR}/consumer-${MONIKER}-sybil

# create directory for double signing node
mkdir $CONS_NODE_SYBIL_DIR
cp -r $CONS_NODE_DIR/* $CONS_NODE_SYBIL_DIR

# clear state in sybil node directory
echo '{"height": "0","round": 0,"step": 0,"signature":"","signbytes":""}' \
    > $CONS_NODE_SYBIL_DIR/data/priv_validator_state.json

# add new node key to sybil
# key was generated using gaiad init
# if the node key is not unique, double signing cannot be achieved
# and errors such as this can be seen in the terminal
# 5:54PM ERR found conflicting vote from ourselves; did you unsafe_reset a validator? height=1961 module=consensus round=0 type=2
# 5:54PM ERR failed to process message err="conflicting votes from validator C888306A908A217B9A943D1DAD8790044D0947A4"
echo '{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"tj55by/yYwruSz4NxsOG9y9k2WrPvKLXKQdz/9jL9Uptmi647OYpcisjwf92TyA+wCUYVDOgW7D53Q+638l9/w=="}}' \
    > $CONS_NODE_SYBIL_DIR/config/node_key.json

# does not use persistent peers; will do a lookup in genesis.json to find peers
# start double signing node - it should not talk to the node with the same key

# Start gaia
interchain-security-cd start \
        --home ${CONS_NODE_SYBIL_DIR} \
        --rpc.laddr tcp://${NODE_IP}:$((RPC_LADDR_PORT+1)) \
        --grpc.address ${NODE_IP}:$((GRPC_LADDR_PORT+1)) \
        --address tcp://${NODE_IP}:$((NODE_ADDRESS_PORT+1)) \
        --p2p.laddr tcp://${NODE_IP}:$((P2P_LADDR_PORT+1)) \
        --grpc-web.enable=false &> ${CONS_NODE_SYBIL_DIR}/logs &

sleep 5

## start Hermes in evidence mode
$HERMES_BIN evidence --chain consumer --check-past-blocks 0 &> $HOME_DIR/hermes-evidence-logs.txt &

sleep 1

# Wait for Hermes to submit double signing evidence
$HERMES_BIN update client --host-chain consumer --client 07-tendermint-0

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
echo "Hermes evidence logs:"
cat $HOME_DIR/hermes-evidence-logs.txt
echo "---------------------------------------------------------------"

exit 1


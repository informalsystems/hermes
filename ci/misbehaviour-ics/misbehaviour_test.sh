#!/bin/bash
set -eux

diag() {
  echo ">>
>> $@
>>" 1>&2
}

# User balance of stake tokens 
USER_COINS="100000000000stake"
# Amount of stake tokens staked
STAKE="100000000stake"
# Node IP address
NODE_IP="127.0.0.1"

# Home directory
HOME_DIR="/tmp/interchain-security"

# Hermes path
HERMES="cargo run -q --"

# Validator moniker
MONIKER="coordinator"

# Validator directory
PROV_NODE_DIR=${HOME_DIR}/provider-${MONIKER}
CONS_NODE_DIR=${HOME_DIR}/consumer-${MONIKER}
CONS_FORK_NODE_DIR=${HOME_DIR}/consumer-fork-${MONIKER}

# Coordinator keys
PROV_KEY1=${MONIKER}-key1
PROV_KEY2=${MONIKER}-key2

# Clean start
pkill -f interchain-security-pd &> /dev/null || true
rm -rf ${PROV_NODE_DIR}

pkill -f interchain-security-cd &> /dev/null || true
rm -rf ${CONS_NODE_DIR}
rm -rf ${CONS_FORK_NODE_DIR}

pkill -f hermes 2> /dev/null || true

# Build genesis file and node directory structure
interchain-security-pd init $MONIKER --chain-id provider --home ${PROV_NODE_DIR}
jq ".app_state.gov.voting_params.voting_period = \"3s\" | .app_state.staking.params.unbonding_time = \"86400s\"" \
   ${PROV_NODE_DIR}/config/genesis.json > \
   ${PROV_NODE_DIR}/edited_genesis.json && mv ${PROV_NODE_DIR}/edited_genesis.json ${PROV_NODE_DIR}/config/genesis.json

sleep 1

# Create account keypairs
interchain-security-pd keys add $PROV_KEY1 --home ${PROV_NODE_DIR} --keyring-backend test --output json > ${PROV_NODE_DIR}/${PROV_KEY1}.json 2>&1
interchain-security-pd keys add $PROV_KEY2 --home ${PROV_NODE_DIR} --keyring-backend test --output json > ${PROV_NODE_DIR}/${PROV_KEY2}.json 2>&1
sleep 1

# Add stake to users
PROV_ACCOUNT_ADDR1=$(jq -r '.address' ${PROV_NODE_DIR}/${PROV_KEY1}.json)
interchain-security-pd add-genesis-account $PROV_ACCOUNT_ADDR1 $USER_COINS --home ${PROV_NODE_DIR} --keyring-backend test
PROV_ACCOUNT_ADDR2=$(jq -r '.address' ${PROV_NODE_DIR}/${PROV_KEY2}.json)
interchain-security-pd add-genesis-account $PROV_ACCOUNT_ADDR2 $USER_COINS --home ${PROV_NODE_DIR} --keyring-backend test
sleep 1


# Stake 1/1000 user's coins
interchain-security-pd gentx $PROV_KEY1 $STAKE --chain-id provider --home ${PROV_NODE_DIR} --keyring-backend test --moniker $MONIKER
# interchain-security-pd gentx $PROV_KEY2 $STAKE --chain-id provider --home ${PROV_NODE_DIR} --keyring-backend test --moniker $MONIKER
sleep 1

interchain-security-pd collect-gentxs --home ${PROV_NODE_DIR} --gentx-dir ${PROV_NODE_DIR}/config/gentx/
sleep 1

sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${NODE_IP}:26658\"/" ${PROV_NODE_DIR}/config/client.toml
sed -i -r 's/timeout_commit = "5s"/timeout_commit = "3s"/g' ${PROV_NODE_DIR}/config/config.toml
sed -i -r 's/timeout_propose = "3s"/timeout_propose = "1s"/g' ${PROV_NODE_DIR}/config/config.toml


# Start gaia
interchain-security-pd start \
    --home ${PROV_NODE_DIR} \
    --rpc.laddr tcp://${NODE_IP}:26658 \
    --grpc.address ${NODE_IP}:9091 \
    --address tcp://${NODE_IP}:26655 \
    --p2p.laddr tcp://${NODE_IP}:26656 \
    --grpc-web.enable=false &> ${PROV_NODE_DIR}/logs &

sleep 5

# Build consumer chain proposal file
tee ${PROV_NODE_DIR}/consumer-proposal.json<<EOF
{
    "title": "Create a chain",
    "description": "Gonna be a great chain",
    "chain_id": "consumer",
    "initial_height": {
        "revision_height": 1
    },
    "genesis_hash": "Z2VuX2hhc2g=",
    "binary_hash": "YmluX2hhc2g=",
    "spawn_time": "2022-03-11T09:02:14.718477-08:00",
    "deposit": "10000001stake",
    "consumer_redistribution_fraction": "0.75",
    "historical_entries": 1000,
    "blocks_per_distribution_transmission": 1000,
    "unbonding_period":  1728000000000000,
    "ccv_timeout_period": 2419200000000000,
    "transfer_timeout_period": 3600000000000
}
EOF

interchain-security-pd keys show $PROV_KEY1 --keyring-backend test --home ${PROV_NODE_DIR}
interchain-security-pd keys show $PROV_KEY2 --keyring-backend test --home ${PROV_NODE_DIR}

# Submit consumer chain proposal
interchain-security-pd tx gov submit-proposal consumer-addition ${PROV_NODE_DIR}/consumer-proposal.json --chain-id provider --from $PROV_KEY1 --home ${PROV_NODE_DIR} --node tcp://${NODE_IP}:26658  --keyring-backend test -b block -y

sleep 1

# Vote yes to proposal
interchain-security-pd tx gov vote 1 yes --from $PROV_KEY1 --chain-id provider --home ${PROV_NODE_DIR} -b block -y --keyring-backend test
# interchain-security-pd tx gov vote 1 yes --from $PROV_KEY2 --chain-id provider --home ${PROV_NODE_DIR} -b block -y --keyring-backend test

sleep 3

## CONSUMER CHAIN ##

# Build genesis file and node directory structure
interchain-security-cd init $MONIKER --chain-id consumer --home  ${CONS_NODE_DIR}
sleep 1

# Create user account keypairs
interchain-security-cd keys add $PROV_KEY1 --home ${CONS_NODE_DIR} --keyring-backend test --output json > ${CONS_NODE_DIR}/${PROV_KEY1}.json 2>&1
interchain-security-cd keys add $PROV_KEY2 --home ${CONS_NODE_DIR} --keyring-backend test --output json > ${CONS_NODE_DIR}/${PROV_KEY2}.json 2>&1

# Add stake to user accounts
CONS_ACCOUNT_ADDR1=$(jq -r '.address' ${CONS_NODE_DIR}/${PROV_KEY1}.json)
interchain-security-cd add-genesis-account $CONS_ACCOUNT_ADDR1 1000000000stake --home ${CONS_NODE_DIR}
CONS_ACCOUNT_ADDR2=$(jq -r '.address' ${CONS_NODE_DIR}/${PROV_KEY2}.json)
interchain-security-cd add-genesis-account $CONS_ACCOUNT_ADDR2 1000000000stake --home ${CONS_NODE_DIR}

# Add consumer genesis states to genesis file
interchain-security-pd query provider consumer-genesis consumer --home ${PROV_NODE_DIR} -o json > consumer_gen.json
jq -s '.[0].app_state.ccvconsumer = .[1] | .[0]' ${CONS_NODE_DIR}/config/genesis.json consumer_gen.json > ${CONS_NODE_DIR}/edited_genesis.json \
&& mv ${CONS_NODE_DIR}/edited_genesis.json ${CONS_NODE_DIR}/config/genesis.json
rm consumer_gen.json

# Create validator states
echo '{"height": "0","round": 0,"step": 0}' > ${CONS_NODE_DIR}/data/priv_validator_state.json

# Copy validator key files
cp ${PROV_NODE_DIR}/config/priv_validator_key.json ${CONS_NODE_DIR}/config/priv_validator_key.json
cp ${PROV_NODE_DIR}/config/node_key.json ${CONS_NODE_DIR}/config/node_key.json

# Set default client port
sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${NODE_IP}:26648\"/" ${CONS_NODE_DIR}/config/client.toml

# Start gaia
interchain-security-cd start --home ${CONS_NODE_DIR} \
        --rpc.laddr tcp://${NODE_IP}:26648 \
        --grpc.address ${NODE_IP}:9081 \
        --address tcp://${NODE_IP}:26645 \
        --p2p.laddr tcp://${NODE_IP}:26646 \
        --grpc-web.enable=false \
        &> ${CONS_NODE_DIR}/logs &

sleep 3

tee $HOME_DIR/config.toml <<EOF
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
ccv_consumer_chain = true
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://${NODE_IP}:9081"
key_name = "relayer"
max_gas = 2000000
rpc_addr = "http://${NODE_IP}:26648"
rpc_timeout = "30s"
store_prefix = "ibc"
trusting_period = "2days"
event_source = { mode = "push", url = "ws://${NODE_IP}:26648/websocket" }

[chains.gas_price]
       denom = "stake"
       price = 0.00

[chains.trust_threshold]
       denominator = "3"
       numerator = "1"

[[chains]]
id = "provider"
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://${NODE_IP}:9091"
key_name = "relayer"
max_gas = 2000000
rpc_addr = "http://${NODE_IP}:26658"
rpc_timeout = "30s"
store_prefix = "ibc"
trusting_period = "2days"
event_source = { mode = "push", url = "ws://${NODE_IP}:26658/websocket" }

[chains.gas_price]
       denom = "stake"
       price = 0.00

[chains.trust_threshold]
       denominator = "3"
       numerator = "1"
EOF

# Delete all previous keys in relayer
$HERMES --config $HOME_DIR/config.toml keys delete --chain consumer --all
$HERMES --config $HOME_DIR/config.toml keys delete --chain provider --all

# Restore keys to hermes relayer
$HERMES --config $HOME_DIR/config.toml keys add --key-name relayer  --key-file ${CONS_NODE_DIR}/${PROV_KEY1}.json --chain consumer
$HERMES --config $HOME_DIR/config.toml keys add --key-name evidence --key-file ${CONS_NODE_DIR}/${PROV_KEY2}.json --chain consumer
$HERMES --config $HOME_DIR/config.toml keys add --key-name relayer  --key-file ${PROV_NODE_DIR}/${PROV_KEY1}.json --chain provider
$HERMES --config $HOME_DIR/config.toml keys add --key-name evidence --key-file ${PROV_NODE_DIR}/${PROV_KEY2}.json --chain provider

sleep 5

$HERMES --config $HOME_DIR/config.toml \
    create connection \
    --a-chain consumer \
    --a-client 07-tendermint-0 \
    --b-client 07-tendermint-0

$HERMES --config $HOME_DIR/config.toml \
    create channel \
    --a-chain consumer \
    --a-port consumer \
    --b-port provider \
    --order ordered \
    --channel-version 1 \
    --a-connection connection-0

sleep 5

$HERMES --config $HOME_DIR/config.toml start &> $HOME_DIR/hermes-logs &

interchain-security-pd q tendermint-validator-set --home ${PROV_NODE_DIR}
interchain-security-cd q tendermint-validator-set --home ${CONS_NODE_DIR}

DELEGATIONS1=$(interchain-security-pd q staking delegations $PROV_ACCOUNT_ADDR1 --home ${PROV_NODE_DIR} -o json)
OPERATOR_ADDR1=$(echo $DELEGATIONS1 | jq -r '.delegation_responses[0].delegation.validator_address')

# DELEGATIONS2=$(interchain-security-pd q staking delegations $PROV_ACCOUNT_ADDR2 --home ${PROV_NODE_DIR} -o json)
# OPERATOR_ADDR2=$(echo $DELEGATIONS2 | jq -r '.delegation_responses[0].delegation.validator_address')

interchain-security-pd tx staking delegate $OPERATOR_ADDR1 1000000stake \
       	--from $PROV_KEY1 \
       	--keyring-backend test \
       	--home ${PROV_NODE_DIR} \
       	--chain-id provider \
	-y -b block

# interchain-security-pd tx staking delegate $OPERATOR_ADDR2 1000000stake \
#        	--from $PROV_KEY2 \
#        	--keyring-backend test \
#        	--home ${PROV_NODE_DIR} \
#        	--chain-id provider \
# 	-y -b block

sleep 13

interchain-security-pd q tendermint-validator-set --home ${PROV_NODE_DIR}
interchain-security-cd q tendermint-validator-set --home ${CONS_NODE_DIR}

##### Fork consumer

tee $HOME_DIR/config_fork.toml<<EOF
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
ccv_consumer_chain = true
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://${NODE_IP}:9071"
key_name = "relayer"
max_gas = 2000000
rpc_addr = "http://${NODE_IP}:26638"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "2days"
event_source = { mode = "push", url = "ws://${NODE_IP}:26638/websocket" }

[chains.gas_price]
       denom = "stake"
       price = 0.00

[chains.trust_threshold]
       denominator = "3"
       numerator = "1"

[[chains]]
id = "provider"
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "tcp://${NODE_IP}:9091"
key_name = "relayer"
max_gas = 2000000
rpc_addr = "http://${NODE_IP}:26658"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "2days"
event_source = { mode = "push", url = "ws://${NODE_IP}:26658/websocket" }

[chains.gas_price]
       denom = "stake"
       price = 0.00

[chains.trust_threshold]
       denominator = "3"
       numerator = "1"
EOF

rm -rf ~/.cometbft-light/
read -r height hash < <(
	curl -s "localhost:26648"/commit \
		| jq -r '(.result//.).signed_header.header.height + " " + (.result//.).signed_header.commit.block_id.hash')
diag "Height: ${height}, Hash: ${hash}"

sleep 10
cp -r ${CONS_NODE_DIR} ${CONS_FORK_NODE_DIR}
# Set default client port
sed -i -r "/node =/ s/= .*/= \"tcp:\/\/${NODE_IP}:26638\"/" ${CONS_FORK_NODE_DIR}/config/client.toml

# Start gaia
interchain-security-cd start --home ${CONS_FORK_NODE_DIR} \
        --rpc.laddr tcp://${NODE_IP}:26638 \
        --grpc.address ${NODE_IP}:9071 \
        --address tcp://${NODE_IP}:26635 \
        --p2p.laddr tcp://${NODE_IP}:26636 \
        --grpc-web.enable=false \
        &> ${CONS_FORK_NODE_DIR}/logs &

sleep 5

# Find trusted state before fork
TRUSTED_HEIGHT=$($HERMES --json --config $HOME_DIR/config.toml query client consensus --chain provider --client 07-tendermint-0 | tail -n 1 | jq '.result[2].revision_height')

# Update client first time 
# FIXME: Why doesn't this one get picked up as evidence of misbehaviour?
$HERMES --config $HOME_DIR/config_fork.toml update client --client 07-tendermint-0 --host-chain provider --trusted-height $TRUSTED_HEIGHT

sleep 10

diag "Updating client on forked chain using trusted height $TRUSTED_HEIGHT"
$HERMES --config $HOME_DIR/config_fork.toml update client --client 07-tendermint-0 --host-chain provider --trusted-height $TRUSTED_HEIGHT


for ((i = 0; i < 10; i++)); do
    # Check the client state on provider and verify it is frozen
    FROZEN_HEIGHT=$($HERMES --config $HOME_DIR/config.toml --json query client state --chain provider --client 07-tendermint-0 | tail -n 1 | jq '.result.frozen_height.revision_height')

    diag "Frozen height: $FROZEN_HEIGHT"

    if [ "$FROZEN_HEIGHT" != "null" ]; then
        diag "Client is frozen, success!"
        exit 0
    else
        diag "Client is not frozen, waiting 5 seconds..."
        sleep 5
    fi
done

diag "Client is not frozen, aborting."
diag "Hermes logs:"
cat $HOME_DIR/hermes-logs
exit 1

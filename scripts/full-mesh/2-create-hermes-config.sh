#!/bin/sh

##############################
## Script setup
##############################

# Fail if there are any errors
set -eu

# Run in a subfolder, not in your $HOME (safeguard against accidental .hermes-deletions)
test "$HOME" != "$(pwd)"
# But if hermes was not run locally, we're going to overcome the issue of not having a --home parameter
ln -s $(pwd)/.hermes $HOME/.hermes || echo "$HOME/.hermes is already set, make sure you link it to .hermes here if you run things locally"

EXPECTED_HERMES_VERSION=0.2.0
DOCKER_IMAGE="informaldev/hermes:${EXPECTED_HERMES_VERSION}"
HERMES="docker run --rm -v $(pwd):/home/hermes --entrypoint /usr/bin/hermes ${DOCKER_IMAGE}"
N="${1:-5}"
echo "N=$N"

##############################
## Create config.toml
##############################

rm -rf .hermes && mkdir .hermes

cat <<EOF > .hermes/config.toml
[global]
strategy = 'naive'
log_level = 'info'

EOF

for i in $(seq 1 "$N")
do
  RPC="$((26000 + 10 * i))"
  GRPC="$((RPC + 2))"

  cat <<EOF >> .hermes/config.toml
[[chains]]
id='network${i}'
rpc_addr='http://localhost:${RPC}'
grpc_addr='https://localhost:${GRPC}'
websocket_addr='ws://localhost:${RPC}/websocket'
rpc_timeout='1s'
account_prefix='cosmos'
key_name='network${i}c0'
store_prefix='ibc'
fee_denom='stake'

[chains.trust_threshold]
numerator = '1'
denominator = '3'

EOF

done

##############################
## Add keys to hermes
##############################

for i in $(seq 1 "$N")
do
  $HERMES keys add "network$i" -f "network${i}/client_wallet_seed.json"
done


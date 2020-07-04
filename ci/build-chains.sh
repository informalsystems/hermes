#!/usr/bin/env bash

## Programmatic list for creating Gaia Hub chains for testing IBC.
## Instead of blindly running this code, read it line by line and understand the dependecies and tasks.
## Prerequisites: Log into Docker Hub
set -eou pipefail
GAIA_BRANCH="master" # Requires a version with the `--keyring-backend` option. v2.1 and above.

echo "*** Requirements"
which git && which go && which make && which sed && which jq && which docker

echo "*** Fetch gaiad source code"
git clone https://github.com/cosmos/gaia || echo "Already cloned."
cd gaia
git checkout "${GAIA_BRANCH}" -q

echo "*** Build binary"
GOOS=linux make build

echo "*** Create config using the built binary"
docker run -it --rm -v $(pwd)/build:/root:z alpine /root/gaiad testnet -o /root/chain_a --v 1 --chain-id chain_A --keyring-backend test
sed -i.bak -e 's/^index_all_keys[[:space:]]*=.*/index_all_keys = true/'   build/chain_a/node0/gaiad/config/config.toml
sed -i.bak -e 's/^timeout_commit[[:space:]]*=.*/timeout_commit = "1s"/'   build/chain_a/node0/gaiad/config/config.toml
sed -i.bak -e 's/^timeout_propose[[:space:]]*=.*/timeout_propose = "1s"/' build/chain_a/node0/gaiad/config/config.toml

docker run -it --rm -v $(pwd)/build:/root:z alpine /root/gaiad testnet -o /root/chain_b --v 1 --chain-id chain_B --keyring-backend test
sed -i.bak -e 's/^index_all_keys[[:space:]]*=.*/index_all_keys = true/'   build/chain_b/node0/gaiad/config/config.toml
sed -i.bak -e 's/^timeout_commit[[:space:]]*=.*/timeout_commit = "1s"/'   build/chain_b/node0/gaiad/config/config.toml
sed -i.bak -e 's/^timeout_propose[[:space:]]*=.*/timeout_propose = "1s"/' build/chain_b/node0/gaiad/config/config.toml

echo "*** Create Docker image and upload to Docker Hub"
cd ..
docker build -t informaldev/chain_a -f chain_a.Dockerfile .
docker build -t informaldev/chain_b -f chain_b.Dockerfile .
docker push informaldev/chain_a
docker push informaldev/chain_b

# Get details from the config files
echo SECRET_A=$(jq -r .secret gaia/build/chain_a/node0/gaiacli/key_seed.json)
echo SECRET_B=$(jq -r .secret gaia/build/chain_b/node0/gaiacli/key_seed.json)
echo NODEID_A=$(jq -r .app_state.genutil.gentxs[0].value.memo  gaia/build/chain_a/node0/gaiad/config/genesis.json)
echo NODEID_B=$(jq -r .app_state.genutil.gentxs[0].value.memo  gaia/build/chain_b/node0/gaiad/config/genesis.json)

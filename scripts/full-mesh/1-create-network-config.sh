#!/bin/sh

##############################
## Script setup
##############################

# Fail if there are any errors
set -eu

# Run in a subfolder, not in your $HOME (safeguard against accidental .gaia-deletions)
test "$HOME" != "$(pwd)"

EXPECTED_GAIAD_VERSION=4.2.1
DOCKER_IMAGE="cephalopodequipment/gaiad:${EXPECTED_GAIAD_VERSION}"
GAIAD="docker run --rm -v $(pwd):/home/gaiad --entrypoint /usr/bin/gaiad ${DOCKER_IMAGE}"
N="${1:-5}"
echo "N=$N"

##############################
## Create gaiad config
##############################

for i in $(seq 1 "$N")
do
  test -d "network$i" && continue
  echo "i=$i"
  $GAIAD testnet --chain-id "network$i" --keyring-backend test --node-dir-prefix "network${i}v" -o . --node-daemon-home . --v 1
  mv "network${i}v0" "network$i"
  mv "gentxs" "network$i"
  $GAIAD keys add "network${i}c0" --keyring-backend test --keyring-dir "network$i" --output json > "network${i}/client_wallet_seed.json"
  $GAIAD add-genesis-account "network${i}c0" "10000000stake,10000network${i}coin" --keyring-backend test --home "network$i"
done

##############################
## Create docker-compose.gaiad.yml
##############################

cat <<EOF > docker-compose.gaiad.yml
services:
EOF

for i in $(seq 1 "$N")
do
  RPC="$((26000 + 10 * i))"
  LEET="$((RPC + 1))"
  GRPC="$((RPC + 2))"
  PP="$((RPC + 3))"

  cat <<EOF >> docker-compose.gaiad.yml
  network${i}:
    container_name: network${i}
    image: "$DOCKER_IMAGE"
    entrypoint: "/usr/bin/gaiad"
    command: start --x-crisis-skip-assert-invariants
    ports:
      - "$RPC:26657"
      - "$LEET:1317"
      - "$GRPC:9090"
      - "$PP:26656"
    volumes:
      - $(pwd)/network${i}:/home/gaiad/.gaia
EOF

done

##############################
## Create full-mesh (default) networks connection graph
##############################

echo "# IBC full-mesh connection graph" > paths

for i in $(seq 1 "$((N-1))")
do
  for j in $(seq "$((i+1))" "$N")
  do
    test $i -eq $j && continue
    echo "$i $j" >> paths
  done
done


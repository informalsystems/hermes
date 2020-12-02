#!/bin/sh

# coins to add to each account
coins="100000000000stake,100000000000samoleans"

echo Node: "$MONIKER"
echo Chain: "$CHAIN_ID"

# Check gaia version
echo "-------------------------------------------------------------------------------------------------------------------"
echo "Gaiad version"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad version --long

# Create home dir
mkdir -p "$HOME_DIR"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Initialize chain $CHAIN_ID"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad init "$MONIKER" --chain-id "$CHAIN_ID" --home "$HOME_DIR"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding validator key"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad keys add validator --keyring-backend="test" --home $HOME_DIR --output json > "$HOME_DIR/validator_seed.json"
cat "$HOME_DIR/validator_seed.json"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding use key"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad keys add user --keyring-backend="test" --home $HOME_DIR --output json > "$HOME_DIR/key_seed.json"
cp "$HOME_DIR/key_seed.json" /data/key_seed_$CHAIN_ID.json
cat "$HOME_DIR/key_seed.json"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding user account to genesis"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad --home $HOME_DIR add-genesis-account $(gaiad --home $HOME_DIR keys --keyring-backend="test" show user -a) $coins
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding validator account to genesis"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad --home $HOME_DIR add-genesis-account $(gaiad --home $HOME_DIR keys --keyring-backend="test" show validator -a) $coins
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Generate a genesis transaction that creates a validator with a self-delegation"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad --home $HOME_DIR gentx validator --keyring-backend="test" --chain-id $CHAIN_ID
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Collect genesis txs and output a genesis.json file"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad collect-gentxs --home $HOME_DIR
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Start the node"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad start \
      --home $HOME_DIR \
      --address tcp://0.0.0.0:$RPC_PORT \
      --p2p.laddr tcp://0.0.0.0:$P2P_PORT \
      --grpc.address="0.0.0.0:$GRPC_PORT" \
      --pruning=nothing


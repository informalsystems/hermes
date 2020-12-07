#!/bin/sh

# coins to add to each account
coins="100000000000stake,100000000000samoleans"

home="/data/$CHAIN_ID"

echo Node: "$MONIKER"
echo Chain: "$CHAIN_ID"
echo Home_Dir: "$home"

# Clean home dir if exists
rm -Rf "$home"

# Create home dir
mkdir -p "$home"

# Check gaia version
echo "-------------------------------------------------------------------------------------------------------------------"
echo "Gaiad version"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad version --long

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Initialize chain $CHAIN_ID"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad init "$MONIKER" --chain-id "$CHAIN_ID" --home "$home"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Replace addresses and ports in the config file"
echo "-------------------------------------------------------------------------------------------------------------------"
sed -i 's#"tcp://127.0.0.1:26657"#"tcp://'"$CHAIN_ID"':'"$RPC_PORT"'"#g' "$home"/config/config.toml
sed -i 's#"tcp://0.0.0.0:26656"#"tcp://'"$CHAIN_ID"':'"$P2P_PORT"'"#g' "$home"/config/config.toml
#sed -i 's#grpc_laddr = ""#grpc_laddr = "tcp://'"$CHAIN_ID"':'"$GRPC_PORT"'"#g' "$home"/config/config.toml

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding validator key"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad keys add validator --keyring-backend="test" --home "$home" --output json > "$home"/validator_seed.json
cat "$home"/validator_seed.json

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding use key"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad keys add user --keyring-backend="test" --home $home --output json > "$home"/key_seed.json
cat "$home"/key_seed.json

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding user account to genesis"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad --home "$home" add-genesis-account $(gaiad --home "$home" keys --keyring-backend="test" show user -a) $coins
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Adding validator account to genesis"
echo "-------------------------------------------------------------------------------------------------------------------"
# shellcheck disable=SC2046
gaiad --home "$home" add-genesis-account $(gaiad --home "$home" keys --keyring-backend="test" show validator -a) $coins
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Generate a genesis transaction that creates a validator with a self-delegation"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad --home "$home" gentx validator --keyring-backend="test" --chain-id "$CHAIN_ID"
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Collect genesis txs and output a genesis.json file"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad collect-gentxs --home "$home"
echo "Done!"

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Start the node"
echo "-------------------------------------------------------------------------------------------------------------------"
gaiad start --home "$home" --pruning=nothing
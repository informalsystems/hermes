#!/bin/sh

set -e

RELAYER_CMD=/usr/bin/hermes

echo "================================================================================================================="
echo "                                              INITIALIZE                                                         "
echo "================================================================================================================="
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Show config path"
echo "-----------------------------------------------------------------------------------------------------------------"
# Configuration file
CONFIG_PATH="$RELAYER_DIR"/"$CONFIG"
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Show relayer version"
echo "-----------------------------------------------------------------------------------------------------------------"
echo Config: "$CONFIG_PATH"
$RELAYER_CMD --config "$CONFIG_PATH" version
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Setting up chains"
echo "-----------------------------------------------------------------------------------------------------------------"
echo "  Chain:" "$CHAIN_A"
echo "    creating chain store folder: "["$CHAIN_A_HOME"]
mkdir -p "$CHAIN_A_HOME"
echo "  Chain:" "$CHAIN_B" ["$CHAIN_B_HOME"]
echo "    creating chain store folder: "["$CHAIN_B_HOME"]
mkdir -p "$CHAIN_B_HOME"
echo Waiting 20 seconds for chains to generate blocks...
sleep 20
echo "================================================================================================================="
echo "                                            CONFIGURATION                                                        "
echo "================================================================================================================="
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Add keys for chains"
echo "-----------------------------------------------------------------------------------------------------------------"
hermes --config "$CONFIG_PATH" keys add --chain "$CHAIN_A" --key-file user_seed_"$CHAIN_A".json
hermes --config "$CONFIG_PATH" keys add --chain "$CHAIN_B" --key-file user_seed_"$CHAIN_B".json
hermes --config "$CONFIG_PATH" keys add --chain "$CHAIN_A" --key-file user2_seed_"$CHAIN_A".json  --key-name user2
hermes --config "$CONFIG_PATH" keys add --chain "$CHAIN_B" --key-file user2_seed_"$CHAIN_B".json  --key-name user2

echo "================================================================================================================="
echo "                                             END-TO-END TESTS                                                    "
echo "================================================================================================================="

python3 /relayer/e2e/run.py -c "$CONFIG_PATH" --cmd "$RELAYER_CMD"


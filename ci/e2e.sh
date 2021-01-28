#!/bin/sh

set -e

RELAYER_CMD=/usr/bin/rrly

echo "================================================================================================================="
echo "                                              INITIALIZE                                                         "
echo "================================================================================================================="
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Show relayer version"
echo "-----------------------------------------------------------------------------------------------------------------"
$RELAYER_CMD version
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Setting up chains"
echo "-----------------------------------------------------------------------------------------------------------------"
# Configuration file
CONFIG_PATH="$RELAYER_DIR"/"$CONFIG"
echo Config: "$CONFIG_PATH"
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
rrly -c "$CONFIG_PATH" keys add "$CHAIN_A" key_seed_"$CHAIN_A".json
rrly -c "$CONFIG_PATH" keys add "$CHAIN_B" key_seed_"$CHAIN_B".json
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Set the primary peers for clients on each chain                                                                  "
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_A="rrly -c $CONFIG_PATH light add tcp://$CHAIN_A:$CHAIN_A_PORT -c $CHAIN_A -s $CHAIN_A_HOME -p -y -f"
echo "Executing: $LIGHT_ADD_CHAIN_A"
bash -c "$LIGHT_ADD_CHAIN_A"
sleep 2
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_B="rrly -c $CONFIG_PATH light add tcp://$CHAIN_B:$CHAIN_B_PORT -c $CHAIN_B -s $CHAIN_B_HOME -p -y -f"
echo "Executing: $LIGHT_ADD_CHAIN_B"
bash -c "$LIGHT_ADD_CHAIN_B"
sleep 2
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Set the secondary peers for clients on each chain                                                                "
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_A_PEER="rrly -c $CONFIG_PATH light add tcp://$CHAIN_A:$CHAIN_A_PORT -c $CHAIN_A -s $CHAIN_A_HOME --peer-id 17D46D8C1576A79203A6733F63B2C9B7235DD559 -y"
echo "Executing: $LIGHT_ADD_CHAIN_A_PEER"
bash -c "$LIGHT_ADD_CHAIN_A_PEER"
sleep 2
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_B_PEER="rrly -c $CONFIG_PATH light add tcp://$CHAIN_B:$CHAIN_B_PORT -c $CHAIN_B -s $CHAIN_B_HOME --peer-id A885BB3D3DFF6101188B462466AE926E7A6CD51E -y"
echo "Executing: $LIGHT_ADD_CHAIN_B_PEER"
bash -c "$LIGHT_ADD_CHAIN_B_PEER"
sleep 2

echo "================================================================================================================="
echo "                                             END-TO-END TESTS                                                    "
echo "================================================================================================================="

python3 ../scripts/e2e.py -c "$CONFIG_PATH" --cmd "$RELAYER_CMD"


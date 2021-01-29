#!/bin/sh

set -e

RELAYER_CMD=/usr/bin/hermes

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
hermes -c "$CONFIG_PATH" keys add "$CHAIN_A" key_seed_"$CHAIN_A".json
hermes -c "$CONFIG_PATH" keys add "$CHAIN_B" key_seed_"$CHAIN_B".json
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Set the primary peers for clients on each chain                                                                  "
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_A="hermes -c $CONFIG_PATH light add tcp://$CHAIN_A:$CHAIN_A_PORT -c $CHAIN_A -s $CHAIN_A_HOME -p -y -f"
echo "Executing: $LIGHT_ADD_CHAIN_A"
bash -c "$LIGHT_ADD_CHAIN_A"
sleep 2
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_B="hermes -c $CONFIG_PATH light add tcp://$CHAIN_B:$CHAIN_B_PORT -c $CHAIN_B -s $CHAIN_B_HOME -p -y -f"
echo "Executing: $LIGHT_ADD_CHAIN_B"
bash -c "$LIGHT_ADD_CHAIN_B"
sleep 2
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Set the secondary peers for clients on each chain                                                                "
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_A_PEER="hermes -c $CONFIG_PATH light add tcp://$CHAIN_A:$CHAIN_A_PORT -c $CHAIN_A -s $CHAIN_A_HOME --peer-id 17D46D8C1576A79203A6733F63B2C9B7235DD559 -y"
echo "Executing: $LIGHT_ADD_CHAIN_A_PEER"
bash -c "$LIGHT_ADD_CHAIN_A_PEER"
sleep 2
echo "-----------------------------------------------------------------------------------------------------------------"
LIGHT_ADD_CHAIN_B_PEER="hermes -c $CONFIG_PATH light add tcp://$CHAIN_B:$CHAIN_B_PORT -c $CHAIN_B -s $CHAIN_B_HOME --peer-id A885BB3D3DFF6101188B462466AE926E7A6CD51E -y"
echo "Executing: $LIGHT_ADD_CHAIN_B_PEER"
bash -c "$LIGHT_ADD_CHAIN_B_PEER"
sleep 2
echo "================================================================================================================="
echo "                                             CLIENTS                                                             "
echo "================================================================================================================="

echo "-----------------------------------------------------------------------------------------------------------------"
echo "Create client transactions"
echo "-----------------------------------------------------------------------------------------------------------------"
echo "Creating $CHAIN_B client on chain $CHAIN_A"
hermes -c "$CONFIG_PATH" tx raw create-client "$CHAIN_A" "$CHAIN_B"
echo "-----------------------------------------------------------------------------------------------------------------"
# shellcheck disable=SC2027
echo "Creating $CHAIN_A client on chain $CHAIN_B"
hermes -c "$CONFIG_PATH" tx raw create-client "$CHAIN_B" "$CHAIN_A"

# TODO: jq -r '.result[].CreateClient.client_id')


#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Query clients"
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "querying "$CHAIN_B"_client on chain "$CHAIN_A"..."
#hermes -c "$CONFIG_PATH" query client state "$CHAIN_A" "$CHAIN_B"_client
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "querying "$CHAIN_A"_client on chain "$CHAIN_B"..."
#hermes -c "$CONFIG_PATH" query client state "$CHAIN_B" "$CHAIN_A"_client
#
#echo "================================================================================================================="
#echo "                                             CONNECTIONS                                                         "
#echo "================================================================================================================="
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Connection Init transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" tx raw conn-init \
#        "$CHAIN_A" \
#        "$CHAIN_B" \
#        "$CHAIN_B"_client \
#        "$CHAIN_A"_client \
#        conn_"$CHAIN_A"_to_"$CHAIN_B" \
#        conn_"$CHAIN_B"_to_"$CHAIN_A"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Connection Open Try transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" tx raw conn-try \
#        "$CHAIN_B" \
#        "$CHAIN_A" \
#        "$CHAIN_A"_client \
#        "$CHAIN_B"_client \
#        conn_"$CHAIN_B"_to_"$CHAIN_A" \
#        conn_"$CHAIN_A"_to_"$CHAIN_B"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Connection Open Ack transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" tx raw conn-ack \
#        "$CHAIN_A" \
#        "$CHAIN_B" \
#        "$CHAIN_B"_client \
#        "$CHAIN_A"_client \
#        conn_"$CHAIN_A"_to_"$CHAIN_B" \
#        conn_"$CHAIN_B"_to_"$CHAIN_A"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Connection Open Confirm transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" tx raw conn-confirm \
#        "$CHAIN_B" \
#        "$CHAIN_A" \
#        "$CHAIN_A"_client \
#        "$CHAIN_B"_client \
#        conn_"$CHAIN_B"_to_"$CHAIN_A" \
#        conn_"$CHAIN_A"_to_"$CHAIN_B"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Query connection - Verify that the two ends are in Open state"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" query connection end "$CHAIN_A" conn_"$CHAIN_A"_to_"$CHAIN_B"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" query connection end "$CHAIN_B" conn_"$CHAIN_B"_to_"$CHAIN_A"
#
#echo "================================================================================================================="
#echo "                                                CHANNELS                                                         "
#echo "================================================================================================================="
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Channel Open Init transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" tx raw chan-init \
#        "$CHAIN_A" \
#        "$CHAIN_B" \
#        conn_"$CHAIN_A"_to_"$CHAIN_B" \
#        transfer \
#        transfer \
#        chan_"$CHAIN_A"_to_"$CHAIN_B" \
#        chan_"$CHAIN_B"_to_"$CHAIN_A"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Channel Open Try transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH"  tx raw chan-try \
#        "$CHAIN_B" \
#        "$CHAIN_A" \
#        conn_"$CHAIN_B"_to_"$CHAIN_A" \
#        transfer \
#        transfer \
#        chan_"$CHAIN_B"_to_"$CHAIN_A" \
#        chan_"$CHAIN_A"_to_"$CHAIN_B"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Channel Open Ack transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" tx raw chan-ack \
#        "$CHAIN_A" \
#        "$CHAIN_B" \
#        conn_"$CHAIN_A"_to_"$CHAIN_B" \
#        transfer \
#        transfer \
#        chan_"$CHAIN_A"_to_"$CHAIN_B" \
#        chan_"$CHAIN_B"_to_"$CHAIN_A"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Channel Open Confirm transaction"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH"  tx raw chan-confirm \
#        "$CHAIN_B" \
#        "$CHAIN_A" \
#        conn_"$CHAIN_B"_to_"$CHAIN_A" \
#        transfer \
#        transfer \
#        chan_"$CHAIN_B"_to_"$CHAIN_A" \
#        chan_"$CHAIN_A"_to_"$CHAIN_B"
#
#echo "-----------------------------------------------------------------------------------------------------------------"
#echo "Query channel - Verify that the two ends are in Open state"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" query channel end "$CHAIN_A" transfer chan_"$CHAIN_A"_to_"$CHAIN_B"
#echo "-----------------------------------------------------------------------------------------------------------------"
#hermes -c "$CONFIG_PATH" query channel end "$CHAIN_B" transfer chan_"$CHAIN_B"_to_"$CHAIN_A"

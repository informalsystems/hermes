#!/bin/sh

# Configuration file
CONFIG_PATH="$RELAYER_DIR"/"$CONFIG"
echo Config: "$CONFIG_PATH"

echo "Setting up relayer for chains:"
echo => Chain: "$CHAIN_A" [$CHAIN_A_HOME]
echo => Chain: "$CHAIN_B" [$CHAIN_B_HOME]
echo Waiting 30 seconds for chains to generate blocks...
sleep 30
echo Done waiting, proceeding...

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Show relayer version"
echo "-------------------------------------------------------------------------------------------------------------------"
rrly version

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Add light clients configuration for chains"
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" light add tcp://"$CHAIN_A":26657 -c "$CHAIN_A" -s "$CHAIN_A_HOME" -p -y --force
sleep 5
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" light add tcp://"$CHAIN_B":26557 -c "$CHAIN_B" -s "$CHAIN_B_HOME" -p -y --force
sleep 5
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" light add tcp://"$CHAIN_B":26557 -c "$CHAIN_A" -s "$CHAIN_A_HOME" -y --force
sleep 5
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" light add tcp://"$CHAIN_A":26657 -c "$CHAIN_B" -s "$CHAIN_B_HOME" -y --force
sleep 5
echo "-------------------------------------------------------------------------------------------------------------------"
echo "Add keys for chains"
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" keys add "$CHAIN_A" "$CHAIN_A_HOME"/key_seed.json
rrly -c "$CONFIG_PATH" keys add "$CHAIN_B" "$CHAIN_A_HOME"/key_seed.json

echo "-------------------------------------------------------------------------------------------------------------------"
echo "Create client transactions"
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" tx raw create-client "$CHAIN_A" "$CHAIN_B" "$CHAIN_B"_client

#!/bin/sh

# Configuration file
CONFIG_PATH="$RELAYER_DIR"/"$CONFIG"
echo Config: "$CONFIG_PATH"

echo "Setting up relayer for chains:"
echo Chain: "$CHAIN_A"
echo Chain: "$CHAIN_B"

echo "-------------------------------------------------------------------------------------------------------------------"
echo " Show relayer version"
echo "-------------------------------------------------------------------------------------------------------------------"
rrly version

echo "-------------------------------------------------------------------------------------------------------------------"
echo " Add light client configuration for chains"
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" light add tcp://$CHAIN_A:26657 -c $CHAIN_A -s /data/$CHAIN_A -p
rrly -c "$CONFIG_PATH" light add tcp://$CHAIN_A:26657 -c $CHAIN_A -s /data/$CHAIN_A
rrly -c "$CONFIG_PATH" light add tcp://$CHAIN_B:26557 -c $CHAIN_B -s /data/$CHAIN_B -p
rrly -c "$CONFIG_PATH" light add tcp://$CHAIN_B:26557 -c $CHAIN_B -s /data/$CHAIN_B

echo "-------------------------------------------------------------------------------------------------------------------"
echo " Add keys for chains"
echo "-------------------------------------------------------------------------------------------------------------------"
rrly -c "$CONFIG_PATH" keys add "$CHAIN_A" /data/"$CHAIN_A"/key_seed.json
rrly -c "$CONFIG_PATH" keys add "$CHAIN_B" /data/"$CHAIN_B"/key_seed.json
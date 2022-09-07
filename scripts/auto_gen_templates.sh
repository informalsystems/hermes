#!/bin/sh

# This script is used to generate the templates for the guide

commands=(
    "clear"
    "config"
    "create"
    "health-check"
    "keys"
    "listen"
    "misbehaviour"
    "query"
    "start"
    "tx"
    "update"
    "upgrade"
    "completions"
    "clear packets"
    "config auto"
    "config validate"
    "create channel"
    "create client"
    "create connection"
    "keys add"
    "keys balance"
    "keys delete"
    "keys list"
    "query channel"
    "query channels"
    "query client"
    "query clients"
    "query connection"
    "query connections"
    "query packet"
    "query transfer"
    "query tx"
    "query channel client"
    "query channel end"
    "query channel ends"
    "query client connections"
    "query client consensus"
    "query client header"
    "query client state"
    "query connection channels"
    "query connection end"
    "query packet ack"
    "query packet acks"
    "query packet commitment"
    "query packet commitments"
    "query packet pending"
    "query packet pending-acks"
    "query packet pending-sends"
    "query transfer denom-trace"
    "query tx events"
    "tx chan-close-confirm"
    "tx chan-close-init"
    "tx chan-open-ack"
    "tx chan-open-confirm"
    "tx chan-open-init"
    "tx chan-open-try"
    "tx conn-confirm"
    "tx conn-init"
    "tx conn-try"
    "tx ft-transfer"
    "tx packet-ack"
    "tx packet-recv"
    "tx upgrade-chain"
    "update client"
    "upgrade client"
    "upgrade clients"
)

HELP_DIR="./guide/src/templates/commands/hermes/help/"

function generate_help(){
    declare -a arr=("${!1}")
    for command in "${arr[@]}"; do
        path=$(echo "$command" | sed -e 's/ /\//g')
        # Check that the command is not empty
        if [ ! -z "$path" ]; then
            # Create the directory (if they don't exist) and the file
            filename="$HELP_DIR$path.md"
            dir="${filename%/*}"
            mkdir -p $dir
            cargo run -q --bin hermes $command --help | sed '1s/.*/DESCRIPTION:/' > $filename &
        fi
    done
    wait
}

generate_help commands[@]
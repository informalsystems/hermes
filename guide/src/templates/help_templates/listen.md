DESCRIPTION:
Listen to and display IBC events emitted by a chain

USAGE:
    hermes listen [OPTIONS] --chain <CHAIN_ID>

OPTIONS:
        --events <EVENT>...    Add an event type to listen for, can be repeated. Listen for all
                               events by default (available: Tx, NewBlock)
    -h, --help                 Print help information

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain to listen for events from

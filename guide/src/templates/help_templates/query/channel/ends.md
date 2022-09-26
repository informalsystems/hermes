DESCRIPTION:
Query channel ends and underlying connection and client objects

USAGE:
    hermes query channel ends [OPTIONS] --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

OPTIONS:
    -h, --help               Print help information
        --height <HEIGHT>    Height of the state to query
        --verbose            Enable verbose output, displaying all details of channels, connections
                             & clients

REQUIRED:
        --chain <CHAIN_ID>        Identifier of the chain to query
        --channel <CHANNEL_ID>    Identifier of the channel to query [aliases: chan]
        --port <PORT_ID>          Identifier of the port to query

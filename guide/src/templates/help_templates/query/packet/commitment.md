DESCRIPTION:
Query packet commitment

USAGE:
    hermes query packet commitment [OPTIONS] --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID> --sequence <SEQUENCE>

OPTIONS:
    -h, --help               Print help information
        --height <HEIGHT>    Height of the state to query. Leave unspecified for latest height.

REQUIRED:
        --chain <CHAIN_ID>        Identifier of the chain to query
        --channel <CHANNEL_ID>    Identifier of the channel to query [aliases: chan]
        --port <PORT_ID>          Identifier of the port to query
        --sequence <SEQUENCE>     Sequence of packet to query [aliases: seq]

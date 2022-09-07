DESCRIPTION:
Query for the header used in a client update at a certain height

USAGE:
    hermes query client header [OPTIONS] --chain <CHAIN_ID> --client <CLIENT_ID> --consensus-height <CONSENSUS_HEIGHT>

OPTIONS:
    -h, --help               Print help information
        --height <HEIGHT>    The chain height context for the query. Leave unspecified for latest
                             height.

REQUIRED:
        --chain <CHAIN_ID>                       Identifier of the chain to query
        --client <CLIENT_ID>                     Identifier of the client to query
        --consensus-height <CONSENSUS_HEIGHT>    Height of header to query

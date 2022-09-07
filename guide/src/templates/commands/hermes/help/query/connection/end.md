DESCRIPTION:
Query connection end

USAGE:
    hermes query connection end [OPTIONS] --chain <CHAIN_ID> --connection <CONNECTION_ID>

OPTIONS:
    -h, --help               Print help information
        --height <HEIGHT>    Height of the state to query. Leave unspecified for latest height.

REQUIRED:
        --chain <CHAIN_ID>              Identifier of the chain to query
        --connection <CONNECTION_ID>    Identifier of the connection to query [aliases: conn]

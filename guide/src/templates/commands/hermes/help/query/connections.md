DESCRIPTION:
Query the identifiers of all connections on a chain

USAGE:
    hermes query connections [OPTIONS] --chain <CHAIN_ID>

OPTIONS:
        --counterparty-chain <COUNTERPARTY_CHAIN_ID>
            Filter the query response by the counterparty chain

    -h, --help
            Print help information

        --verbose
            Enable verbose output, displaying the client for each connection in the response

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain to query

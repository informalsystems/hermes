DESCRIPTION:
Query the identifiers of all channels on a given chain

USAGE:
    hermes query channels [OPTIONS] --chain <CHAIN_ID>

OPTIONS:
        --counterparty-chain <COUNTERPARTY_CHAIN_ID>
            Filter the query response by the this counterparty chain

    -h, --help
            Print help information

        --show-counterparty
            Show the counterparty chain, port, and channel

        --verbose
            Enable verbose output, displaying the client and connection ids for each channel in the
            response

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain to query

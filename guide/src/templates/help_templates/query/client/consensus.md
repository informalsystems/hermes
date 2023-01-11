DESCRIPTION:
Query the client consensus state

USAGE:
    hermes query client consensus [OPTIONS] --chain <CHAIN_ID> --client <CLIENT_ID>

OPTIONS:
        --consensus-height <CONSENSUS_HEIGHT>
            Height of the client's consensus state to query

    -h, --help
            Print help information

        --height <HEIGHT>
            The chain height context to be used, applicable only to a specific height

REQUIRED:
        --chain <CHAIN_ID>      Identifier of the chain to query
        --client <CLIENT_ID>    Identifier of the client to query

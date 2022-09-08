DESCRIPTION:
Query the identifiers of all clients on a chain

USAGE:
    hermes query clients [OPTIONS] --host-chain <HOST_CHAIN_ID>

OPTIONS:
    -h, --help
            Print help information

        --omit-chain-ids
            Omit printing the reference (or target) chain for each client

        --reference-chain <REFERENCE_CHAIN_ID>
            Filter for clients which target a specific chain id (implies '--omit-chain-ids')

REQUIRED:
        --host-chain <HOST_CHAIN_ID>    Identifier of the chain to query

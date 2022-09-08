DESCRIPTION:
Create a new connection between two chains

USAGE:
    hermes create connection [OPTIONS] --A_CHAIN_ID <A_CHAIN_ID> --b-chain <B_CHAIN_ID>

    hermes create connection [OPTIONS] --A_CHAIN_ID <A_CHAIN_ID> --a-client <A_CLIENT_ID> --b-client <B_CLIENT_ID>

OPTIONS:
        --delay <DELAY>    Delay period parameter for the new connection (seconds) [default: 0]
    -h, --help             Print help information

FLAGS:
        --A_CHAIN_ID <A_CHAIN_ID>      Identifier of the side `a` chain for the new connection
        --a-client <A_CLIENT_ID>    Identifier of client hosted on chain `a`; default: None (creates
                                    a new client)
        --b-chain <B_CHAIN_ID>      Identifier of the side `b` chain for the new connection
        --b-client <B_CLIENT_ID>    Identifier of client hosted on chain `b`; default: None (creates
                                    a new client)

DESCRIPTION:
Relay the connection attempt (ConnectionOpenTry)

USAGE:
    hermes tx conn-try [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --dst-client <DST_CLIENT_ID> --src-client <SRC_CLIENT_ID> --src-connection <SRC_CONNECTION_ID>

OPTIONS:
        --dst-connection <DST_CONNECTION_ID>
            Identifier of the destination connection (optional) [aliases: dst-conn]

    -h, --help
            Print help information

REQUIRED:
        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --dst-client <DST_CLIENT_ID>
            Identifier of the destination client

        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-client <SRC_CLIENT_ID>
            Identifier of the source client

        --src-connection <SRC_CONNECTION_ID>
            Identifier of the source connection (required) [aliases: src-conn]

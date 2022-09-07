DESCRIPTION:
Confirm opening of a connection (ConnectionOpenConfirm)

USAGE:
    hermes tx conn-confirm --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --dst-client <DST_CLIENT_ID> --src-client <SRC_CLIENT_ID> --dst-connection <DST_CONNECTION_ID> --src-connection <SRC_CONNECTION_ID>

OPTIONS:
    -h, --help    Print help information

REQUIRED:
        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --dst-client <DST_CLIENT_ID>
            Identifier of the destination client

        --dst-connection <DST_CONNECTION_ID>
            Identifier of the destination connection (required) [aliases: dst-conn]

        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-client <SRC_CLIENT_ID>
            Identifier of the source client

        --src-connection <SRC_CONNECTION_ID>
            Identifier of the source connection (required) [aliases: src-conn]

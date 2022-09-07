DESCRIPTION:
Confirm the closing of a channel (ChannelCloseConfirm)

USAGE:
    hermes tx chan-close-confirm --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --dst-connection <DST_CONNECTION_ID> --dst-port <DST_PORT_ID> --src-port <SRC_PORT_ID> --dst-channel <DST_CHANNEL_ID> --src-channel <SRC_CHANNEL_ID>

OPTIONS:
    -h, --help    Print help information

REQUIRED:
        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --dst-channel <DST_CHANNEL_ID>
            Identifier of the destination channel (required) [aliases: dst-chan]

        --dst-connection <DST_CONNECTION_ID>
            Identifier of the destination connection [aliases: dst-conn]

        --dst-port <DST_PORT_ID>
            Identifier of the destination port

        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-channel <SRC_CHANNEL_ID>
            Identifier of the source channel (required) [aliases: src-chan]

        --src-port <SRC_PORT_ID>
            Identifier of the source port

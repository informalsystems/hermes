DESCRIPTION:
Relay the channel upgrade attempt (ChannelUpgradeAck)

USAGE:
    hermes tx chan-upgrade-ack [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --dst-connection <DST_CONNECTION_ID> --dst-port <DST_PORT_ID> --src-port <SRC_PORT_ID> --src-channel <SRC_CHANNEL_ID>

OPTIONS:
        --dst-channel <DST_CHANNEL_ID>
            Identifier of the destination channel (optional) [aliases: dst-chan]

    -h, --help
            Print help information

        --timeout-height <TIMEOUT_HEIGHT>
            Height that, once it has been surpassed on the originating chain, the upgrade will time
            out. Required if no timeout timestamp is specified.

        --timeout-timestamp <TIMEOUT_TIMESTAMP>
            Timestamp that, once it has been surpassed on the originating chain, the upgrade will
            time out. Required if no timeout height is specified.

REQUIRED:
        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

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

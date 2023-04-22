DESCRIPTION:
Initiate a channel upgrade (ChannelUpgradeInit)

Build and send a `ChannelUpgradeInit` message to a destination chain that the source chain has an
already-existing channel open with, signaling the intent by the source chain to perform the channel
upgrade handshake.

USAGE:
    hermes tx chan-upgrade-init [OPTIONS] --src-chain <SRC_CHAIN_ID> --dst-chain <DST_CHAIN_ID> --dst-port <DST_PORT_ID> --dst-channel <DST_CHANNEL_ID>

OPTIONS:
        --connection-hops <CONNECTION_HOPS>
            Set of connection hops for the channel that both chains will upgrade to. Defaults to the
            connection hops of the initiating chain if not specified.

    -h, --help
            Print help information

        --ordering <ORDERING>
            Ordering of the channel that both chains will upgrade to. Note that the a channel may
            only be upgraded from a stricter ordering to a less strict ordering, i.e., from ORDERED
            to UNORDERED. Defaults to the ordering of the initiating chain if not specified.

        --timeout-height <TIMEOUT_HEIGHT>
            Height that, once it has been surpassed on the originating chain, the upgrade will time
            out. Required if no timeout timestamp is specified.

        --timeout-timestamp <TIMEOUT_TIMESTAMP>
            Timestamp that, once it has been surpassed on the originating chain, the upgrade will
            time out. Required if no timeout height is specified.

        --version <VERSION>
            Version of the channel that both chains will upgrade to. Defaults to the version of the
            initiating chain if not specified.

REQUIRED:
        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --dst-channel <DST_CHANNEL_ID>
            Identifier of the destination channel
            
            [aliases: dst-chan]

        --dst-port <DST_PORT_ID>
            Identifier of the destination port

        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

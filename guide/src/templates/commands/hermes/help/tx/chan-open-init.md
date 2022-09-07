DESCRIPTION:
Initialize a channel (ChannelOpenInit)

USAGE:
    hermes tx chan-open-init [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --dst-connection <DST_CONNECTION_ID> --dst-port <DST_PORT_ID> --src-port <SRC_PORT_ID>

OPTIONS:
    -h, --help             Print help information
        --order <ORDER>    The channel ordering, valid options 'unordered' (default) and 'ordered'
                           [default: ORDER_UNORDERED]

REQUIRED:
        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --dst-connection <DST_CONNECTION_ID>
            Identifier of the destination connection [aliases: dst-conn]

        --dst-port <DST_PORT_ID>
            Identifier of the destination port

        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-port <SRC_PORT_ID>
            Identifier of the source port

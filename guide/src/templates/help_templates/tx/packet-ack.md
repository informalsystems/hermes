DESCRIPTION:
Relay acknowledgment packets

USAGE:
    hermes tx packet-ack [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --src-port <SRC_PORT_ID> --src-channel <SRC_CHANNEL_ID>

OPTIONS:
    -h, --help
            Print help information

        --packet-data-query-height <PACKET_DATA_QUERY_HEIGHT>
            Exact height at which the packet data is queried via block_results RPC

REQUIRED:
        --dst-chain <DST_CHAIN_ID>        Identifier of the destination chain
        --src-chain <SRC_CHAIN_ID>        Identifier of the source chain
        --src-channel <SRC_CHANNEL_ID>    Identifier of the source channel [aliases: src-chan]
        --src-port <SRC_PORT_ID>          Identifier of the source port

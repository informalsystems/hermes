DESCRIPTION:
Relay receive or timeout packets

USAGE:
    hermes tx packet-recv [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --src-port <SRC_PORT_ID> --src-channel <SRC_CHANNEL_ID>

OPTIONS:
    -h, --help
            Print help information

        --packet-data-query-height <PACKET_DATA_QUERY_HEIGHT>
            Exact height at which the packet data is queried via block_results RPC

        --packet-sequences <PACKET_SEQUENCES>
            Sequences of packets to be cleared on `dst-chain`. Either a single sequence or a range
            of sequences can be specified. If not provided, all pending recv or timeout packets will
            be cleared. Each element of the comma-separated list must be either a single sequence or
            a range of sequences. Example: `1,10..20` will clear packets with sequences 1, 10, 11,
            ..., 20

REQUIRED:
        --dst-chain <DST_CHAIN_ID>        Identifier of the destination chain
        --src-chain <SRC_CHAIN_ID>        Identifier of the source chain
        --src-channel <SRC_CHANNEL_ID>    Identifier of the source channel [aliases: src-chan]
        --src-port <SRC_PORT_ID>          Identifier of the source port

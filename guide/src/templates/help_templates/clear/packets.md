DESCRIPTION:
Clear outstanding packets (i.e., packet-recv and packet-ack) on a given channel in both directions.
The channel is identified by the chain, port, and channel IDs at one of its ends

USAGE:
    hermes clear packets [OPTIONS] --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

OPTIONS:
        --counterparty-key-name <COUNTERPARTY_KEY_NAME>
            use the given signing key for the counterparty chain (default: `counterparty_key_name`
            config)

    -h, --help
            Print help information

        --key-name <KEY_NAME>
            use the given signing key for the specified chain (default: `key_name` config)

        --packet-sequences <PACKET_SEQUENCES>
            Sequences of packets to be cleared on the specified chain

        --query-packets-chunk-size <QUERY_PACKETS_CHUNK_SIZE>
            number of packets to fetch at once from the chain (default: `query_packets_chunk_size`
            config)

REQUIRED:
        --chain <CHAIN_ID>        Identifier of the chain
        --channel <CHANNEL_ID>    Identifier of the channel
        --port <PORT_ID>          Identifier of the port

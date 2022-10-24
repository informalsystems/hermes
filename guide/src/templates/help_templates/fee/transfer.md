DESCRIPTION:
Perform a token transfer supported with a fee

USAGE:
    hermes fee transfer [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --src-port <SRC_PORT_ID> --src-channel <SRC_CHANNEL_ID> --amount <AMOUNT>

OPTIONS:
        --ack-fee <ACK_FEE>
            Fee to pay for the Ack message. Default: 0 [default: 0]

        --denom <DENOM>
            Denomination of the coins to send. Default: samoleans [default: samoleans]

    -h, --help
            Print help information

        --key-name <KEY_NAME>
            Use the given signing key name (default: `key_name` config)

        --number-msgs <NUMBER_MSGS>
            Number of messages to send

        --receive-fee <RECEIVE_FEE>
            Fee to pay for the Recv message. Default: 0 [default: 0]

        --recipient <RECIPIENT>
            The account address on the destination chain which will receive the tokens. If omitted,
            the relayer's wallet on the destination chain will be used

        --timeout-fee <TIMEOUT_FEE>
            Fee to pay for the Timeout message. Default: 0 [default: 0]

        --timeout-height-offset <TIMEOUT_HEIGHT_OFFSET>
            Timeout in number of blocks since current. Default: 0 [default: 0]

        --timeout-seconds <TIMEOUT_SECONDS>
            Timeout in seconds since current. Default: 0 [default: 0]

FLAGS:
        --amount <AMOUNT>
            Amount of coins (samoleans, by default) to send (e.g. `100000`)

        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-channel <SRC_CHANNEL_ID>
            Identifier of the source channel [aliases: src-chan]

        --src-port <SRC_PORT_ID>
            Identifier of the source port

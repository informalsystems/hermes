DESCRIPTION:
Send a fungible token transfer test transaction (ICS20 MsgTransfer)

USAGE:
    hermes tx ft-transfer [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --src-port <SRC_PORT_ID> --src-channel <SRC_CHANNEL_ID> --amount <AMOUNT>

OPTIONS:
        --denom <DENOM>
            Denomination of the coins to send [default: samoleans]

    -h, --help
            Print help information

        --key-name <KEY_NAME>
            Use the given signing key name (default: `key_name` config)

        --memo <MEMO>
            Optional memo included in the transfer

        --number-msgs <NUMBER_MSGS>
            Number of messages to send

        --receiver <RECEIVER>
            The account address on the destination chain which will receive the tokens. If omitted,
            the relayer's wallet on the destination chain will be used

        --timeout-height-offset <TIMEOUT_HEIGHT_OFFSET>
            Timeout in number of blocks since current [default: 0]

        --timeout-seconds <TIMEOUT_SECONDS>
            Timeout in seconds since current [default: 0]

REQUIRED:
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

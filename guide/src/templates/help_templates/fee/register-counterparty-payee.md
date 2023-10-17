DESCRIPTION:
Register a counterparty payee for a channel

USAGE:
    hermes fee register-counterparty-payee --chain <CHAIN_ID> --channel <CHANNEL_ID> --port <PORT_ID> --counterparty-payee <COUNTERPARTY_PAYEE_ADDRESS>

OPTIONS:
    -h, --help    Print help information

FLAGS:
        --chain <CHAIN_ID>
            Identifier of the chain

        --channel <CHANNEL_ID>
            Identifier of the channel [aliases: chan]

        --counterparty-payee <COUNTERPARTY_PAYEE_ADDRESS>
            Address of the counterparty payee.
            
            Note that there exists a configuration parameter `auto_register_counterparty_payee` that
            can be enabled in order to have Hermes automatically register the counterparty payee on
            the destination chain to the relayer's address on the source chain. This option can be
            used for simple configuration of the relayer to receive fees for relaying RecvPackets on
            fee-enabled channels.

        --port <PORT_ID>
            Identifier of the port

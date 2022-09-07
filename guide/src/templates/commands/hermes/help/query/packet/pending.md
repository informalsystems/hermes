DESCRIPTION:
Output a summary of pending packets in both directions

USAGE:
    hermes query packet pending --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

OPTIONS:
    -h, --help    Print help information

REQUIRED:
        --chain <CHAIN_ID>        Identifier of the chain at one end of the channel
        --channel <CHANNEL_ID>    Channel identifier on the chain given by <CHAIN_ID> [aliases:
                                  chan]
        --port <PORT_ID>          Port identifier on the chain given by <CHAIN_ID>

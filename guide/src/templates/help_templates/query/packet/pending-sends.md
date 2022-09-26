DESCRIPTION:
Query pending send packets

USAGE:
    hermes query packet pending-sends --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

OPTIONS:
    -h, --help    Print help information

REQUIRED:
        --chain <CHAIN_ID>        Identifier of the chain for the unreceived sequences
        --channel <CHANNEL_ID>    Channel identifier [aliases: chan]
        --port <PORT_ID>          Port identifier

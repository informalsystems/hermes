DESCRIPTION:
Query pending acknowledgments

USAGE:
    hermes query packet pending-acks --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

OPTIONS:
    -h, --help    Print help information

REQUIRED:
        --chain <CHAIN_ID>        Identifier of the chain to query the unreceived acknowledgments
        --channel <CHANNEL_ID>    Channel identifier [aliases: chan]
        --port <PORT_ID>          Port identifier

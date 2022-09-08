DESCRIPTION:
Clear objects, such as outstanding packets on a channel

USAGE:
    hermes clear <SUBCOMMAND>

OPTIONS:
    -h, --help    Print help information

SUBCOMMANDS:
    help       Print this message or the help of the given subcommand(s)
    packets    Clear outstanding packets (i.e., packet-recv and packet-ack) on a given channel
                   in both directions. The channel is identified by the chain, port, and channel IDs
                   at one of its ends

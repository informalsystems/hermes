DESCRIPTION:
Create and send IBC transactions

USAGE:
    hermes tx <SUBCOMMAND>

OPTIONS:
    -h, --help    Print help information

SUBCOMMANDS:
    chan-close-confirm    Confirm the closing of a channel (ChannelCloseConfirm)
    chan-close-init       Initiate the closing of a channel (ChannelCloseInit)
    chan-open-ack         Relay acknowledgment of a channel attempt (ChannelOpenAck)
    chan-open-confirm     Confirm opening of a channel (ChannelOpenConfirm)
    chan-open-init        Initialize a channel (ChannelOpenInit)
    chan-open-try         Relay the channel attempt (ChannelOpenTry)
    conn-ack              Relay acknowledgment of a connection attempt (ConnectionOpenAck)
    conn-confirm          Confirm opening of a connection (ConnectionOpenConfirm)
    conn-init             Initialize a connection (ConnectionOpenInit)
    conn-try              Relay the connection attempt (ConnectionOpenTry)
    ft-transfer           Send a fungible token transfer test transaction (ICS20 MsgTransfer)
    help                  Print this message or the help of the given subcommand(s)
    packet-ack            Relay acknowledgment packets
    packet-recv           Relay receive or timeout packets
    upgrade-chain         Send an IBC upgrade plan

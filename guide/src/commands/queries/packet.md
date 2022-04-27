
# Packet Queries

Use the `query packet` commands to query information about packets.


```shell
USAGE:
    hermes query packet <SUBCOMMAND>

OPTIONS:
    -h, --help    Print help information

SUBCOMMANDS:
    ack                   Query packet acknowledgment
    acks                  Query packet acknowledgments
    commitment            Query packet commitment
    commitments           Query packet commitments
    pending               Output a summary of pending packets in both directions
    unreceived-acks       Query unreceived acknowledgments
    unreceived-packets    Query unreceived packets
    help                  Print this message or the help of the given subcommand(s)
```

## Table of Contents

<!-- toc -->


## Pending Packets

Use the `query packet pending` command to query the sequence numbers of all packets that have not yet been received or acknowledged, at both ends of a channel.

```shell
USAGE:
    hermes query packet pending <CHAIN_ID> <PORT_ID> <CHANNEL_ID>

ARGS:
    <CHAIN_ID>      identifier of the chain at one end of the channel
    <PORT_ID>       port identifier on the chain given by <CHAIN_ID>
    <CHANNEL_ID>    channel identifier on the chain given by <CHAIN_ID>
```

__Example__

Query the sequence numbers of all packets that either not yet been received or not yet been acknowledged, at both ends of the channel `channel-1`.

```shell
$ hermes query packet pending ibc-0 tranfer channel-1
```

```json
Success: Summary {
    forward: PendingPackets {
        unreceived_packets: [
            2203,
            ...
            2212,
        ],
        unreceived_acks: [
           2183,
           ...
           2202,
        ],
    },
    reverse: PendingPackets {
        unreceived_packets: [
           14,
           ...
           23,
        ],
        unreceived_acks: [
           4,
           ...
           13,
        ],
    },
}
```


## Packet Commitments

Use the `query packet commitments` command to query the sequence numbers of all packets that have been sent but not yet acknowledged (these are the packets that still have their commitments stored).

```shell
USAGE:
    hermes query packet commitments <OPTIONS>

DESCRIPTION:
    Query packet commitments

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
```

__Example__

Query `ibc-0` for the sequence numbers of packets that still have commitments on `ibc-0` and that were sent on `transfer` port and `channel-0`:

```shell
hermes query packet commitments ibc-0 transfer channel-0
```

```json
Success: PacketSeqs {
    height: Height {
        revision: 0,
        height: 9154,
    },
    seqs: [
        1,
        2,
        3
    ],
}
```

## Packet Commitment with Sequence

Use the `query packet commitment` command to query the commitment value of a packet with a given sequence number.

```shell
USAGE:
    hermes query packet commitment <OPTIONS>

DESCRIPTION:
    Query packet commitment

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
    sequence                  sequence of packet to query

FLAGS:
    -H, --height HEIGHT       height of the state to query
```

__Example__

Query `ibc-0` for the commitment of packet with sequence `3` sent on `transfer` port and `channel-0`:

```shell
hermes query packet commitment ibc-0 transfer channel-0 3
```

```json
Success: "F9458DC7EBEBCD6D18E983FCAB5BD752CC2A74532BBD50B812DB229997739EFC"
```

## Packet Acknowledgments

Use the `query packet acknowledgments` command to query the sequence numbers of all packets that have been acknowledged.

```shell
USAGE:
    hermes query packet acks <OPTIONS>

DESCRIPTION:
    Query packet acknowledgments

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
```

__Example__

Query `ibc-1` for the sequence numbers of packets acknowledged that were received on `transfer` port and `channel-1`:

```shell
hermes query packet acks ibc-1 transfer channel-1
```

```json
Success: PacketSeqs {
    height: Height {
        revision: 1,
        height: 9547,
    },
    seqs: [
        1,
        2,
        3
    ],
}
```

## Packet Acknowledgment with Sequence

Use the `query packet acknowledgment` command to query the acknowledgment value of a packet with a given sequence number.

```shell
USAGE:
    hermes query packet ack <OPTIONS>

DESCRIPTION:
    Query packet acknowledgment

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
    sequence                  sequence of packet to query

FLAGS:
    -H, --height HEIGHT       height of the state to query
```

__Example__

Query `ibc-1` for the acknowledgment of packet with sequence `2` received on `transfer` port and `channel-1`:

```shell
hermes query packet ack ibc-1 transfer channel-1 2
```

```json
Success: "08F7557ED51826FE18D84512BF24EC75001EDBAF2123A477DF72A0A9F3640A7C"
```

## Unreceived Packets

Use the `query packet unreceived-packets` command to query the sequence numbers of all packets that have been sent on the source chain but not yet received on the destination chain.

```shell
USAGE:
    hermes query packet unreceived-packets <OPTIONS>

DESCRIPTION:
    Query unreceived packets

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain for the unreceived sequences
    port_id                   port identifier
    channel_id                channel identifier
```

__Example__

Query `transfer` port and `channel-1` on `ibc-1` for the sequence numbers of packets sent on `ibc-0` but not yet received:

```shell
hermes query packet unreceived-packets ibc-1 transfer channel-1
```

```json
Success: [
    1,
    2,
    3
]
```

## Unreceived Acknowledgments

Use the `query packet unreceived-acks` command to query the sequence numbers of all packets that have not yet been acknowledged.

```shell
USAGE:
    hermes query packet unreceived-acks <OPTIONS>

DESCRIPTION:
    Query unreceived acknowledgments

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query the unreceived acknowledgments
    port_id                   port identifier
    channel_id                channel identifier
```

__Example__

Query `transfer` port and `channel-0` on `ibc-0` for the sequence numbers of packets received by `ibc-1` but not yet acknowledged on `ibc-0`:

```shell
hermes query packet unreceived-acks ibc-0 transfer channel-0
```

```json
Success: [
    1,
    2,
    3
]
```

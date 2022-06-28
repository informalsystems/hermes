
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
```

## Table of Contents

<!-- toc -->


## Pending Packets

Use the `query packet pending` command to query the sequence numbers of all packets that have not yet been received or acknowledged, at both ends of a channel.

```shell
USAGE:
    hermes query packet pending --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

FLAGS:
        --chain <CHAIN_ID>        Identifier of the chain at one end of the channel
        --channel <CHANNEL_ID>    Channel identifier on the chain given by <CHAIN_ID>
        --port <PORT_ID>          Port identifier on the chain given by <CHAIN_ID>
```

__Example__

Query the sequence numbers of all packets that either not yet been received or not yet been acknowledged, at both ends of the channel `channel-1`.

```shell
$ hermes query packet pending --chain ibc-0 --port transfer --channel channel-1
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
    hermes query packet commitments --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

DESCRIPTION:
    Query packet commitments

FLAGS:
        --chain <CHAIN_ID>        Identifier of the chain to query
        --channel <CHANNEL_ID>    Identifier of the channel to query
        --port <PORT_ID>          Identifier of the port to query
```

__Example__

Query `ibc-0` for the sequence numbers of packets that still have commitments on `ibc-0` and that were sent on `transfer` port and `channel-0`:

```shell
hermes query packet commitments --chain ibc-0 --port transfer --channel channel-0
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
    hermes query packet commitment [OPTIONS] --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID> --sequence <SEQUENCE>

DESCRIPTION:
    Query packet commitment

FLAGS:
        --chain <CHAIN_ID>             Identifier of the chain to query
        --channel <CHANNEL_ID>         Identifier of the channel to query
        --port <PORT_ID>               Identifier of the port to query
        --sequence <SEQUENCE>          Sequence of packet to query

OPTIONS:
        --height <HEIGHT>              Height of the state to query
```

__Example__

Query `ibc-0` for the commitment of packet with sequence `3` sent on `transfer` port and `channel-0`:

```shell
hermes query packet commitment --chain ibc-0 --port transfer --channel channel-0 --sequence 3
```

```json
Success: "F9458DC7EBEBCD6D18E983FCAB5BD752CC2A74532BBD50B812DB229997739EFC"
```

## Packet Acknowledgments

Use the `query packet acknowledgments` command to query the sequence numbers of all packets that have been acknowledged.

```shell
USAGE:
    hermes query packet acks --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

DESCRIPTION:
    Query packet acknowledgments

FLAGS:
        --chain <CHAIN_ID>        Identifier of the chain to query
        --channel <CHANNEL_ID>    Identifier of the channel to query
        --port <PORT_ID>          Identifier of the port to query
```

__Example__

Query `ibc-1` for the sequence numbers of packets acknowledged that were received on `transfer` port and `channel-1`:

```shell
hermes query packet acks --chain ibc-1 --port transfer --channel channel-1
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
    hermes query packet ack [OPTIONS] --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID> --sequence <SEQUENCE>

DESCRIPTION:
    Query packet acknowledgment

FLAGS:
        --chain <CHAIN_ID>             Identifier of the chain to query
        --channel <CHANNEL_ID>         Identifier of the channel to query
        --port <PORT_ID>               Identifier of the port to query
        --sequence <SEQUENCE>          Sequence of packet to query

OPTIONS:
        --height <HEIGHT>              Height of the state to query
```

__Example__

Query `ibc-1` for the acknowledgment of packet with sequence `2` received on `transfer` port and `channel-1`:

```shell
hermes query packet ack --chain ibc-1 --port transfer --channel channel-1 --sequence 2
```

```json
Success: "08F7557ED51826FE18D84512BF24EC75001EDBAF2123A477DF72A0A9F3640A7C"
```

## Unreceived Packets

Use the `query packet unreceived-packets` command to query the sequence numbers of all packets that have been sent on the source chain but not yet received on the destination chain.

```shell
USAGE:
    hermes query packet unreceived-packets --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

DESCRIPTION:
    Query unreceived packets

FLAGS:
        --chain <CHAIN_ID>        Identifier of the chain for the unreceived sequences
        --channel <CHANNEL_ID>    Channel identifier
        --port <PORT_ID>          Port identifier
```

__Example__

Query `transfer` port and `channel-1` on `ibc-1` for the sequence numbers of packets sent on `ibc-0` but not yet received:

```shell
hermes query packet unreceived-packets --chain ibc-1 --port transfer --channel channel-1
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
    hermes query packet unreceived-acks --chain <CHAIN_ID> --port <PORT_ID> --channel <CHANNEL_ID>

DESCRIPTION:
    Query unreceived acknowledgments

FLAGS:
        --chain <CHAIN_ID>        Identifier of the chain to query the unreceived acknowledgments
        --channel <CHANNEL_ID>    Channel identifier
        --port <PORT_ID>          Port identifier
```

__Example__

Query `transfer` port and `channel-0` on `ibc-0` for the sequence numbers of packets received by `ibc-1` but not yet acknowledged on `ibc-0`:

```shell
hermes query packet unreceived-acks --chain ibc-0 --port transfer --channel channel-0
```

```json
Success: [
    1,
    2,
    3
]
```

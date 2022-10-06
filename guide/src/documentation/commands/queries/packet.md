
# Packet Queries

Use the `query packet` commands to query information about packets.


```shell
{{#include ../../../templates/help_templates/query/packet.md}}
```

## Table of Contents

<!-- toc -->


## Pending Packets

Use the `query packet pending` command to query the sequence numbers of all packets that have not yet been received or acknowledged, at both ends of a channel.

```shell
{{#include ../../../templates/help_templates/query/packet/pending.md}}
```

__Example__

Query the sequence numbers of all packets that either not yet been received or not yet been acknowledged, at both ends of the channel `channel-1`.

```shell
{{#template ../../../templates/commands/hermes/query/packet/pending_1.md CHAIN_ID=ibc-0 PORT_ID=transfer CHANNEL_ID=channel-1}}
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
{{#include ../../../templates/help_templates/query/packet/commitments.md}}
```

__Example__

Query `ibc-0` for the sequence numbers of packets that still have commitments on `ibc-0` and that were sent on `transfer` port and `channel-0`:

```shell
{{#template ../../../templates/commands/hermes/query/packet/commitments_1.md CHAIN_ID=ibc-0 PORT_ID=transfer CHANNEL_ID=channel-0}}
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
{{#include ../../../templates/help_templates/query/packet/commitment.md}}
```

__Example__

Query `ibc-0` for the commitment of packet with sequence `3` sent on `transfer` port and `channel-0`:

```shell
{{#template ../../../templates/commands/hermes/query/packet/commitment_1.md CHAIN_ID=ibc-0 PORT_ID=transfer CHANNEL_ID=channel-0 SEQUENCE=3}}
```

```json
Success: "F9458DC7EBEBCD6D18E983FCAB5BD752CC2A74532BBD50B812DB229997739EFC"
```

## Packet Acknowledgments

Use the `query packet acks` command to query the sequence numbers of all packets that have been acknowledged.

```shell
{{#include ../../../templates/help_templates/query/packet/acks.md}}
```

__Example__

Query `ibc-1` for the sequence numbers of packets acknowledged that were received on `transfer` port and `channel-1`:

```shell
{{#template ../../../templates/commands/hermes/query/packet/acks_1.md CHAIN_ID=ibc-1 PORT_ID=transfer CHANNEL_ID=channel-1}}
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
{{#include ../../../templates/help_templates/query/packet/ack.md}}
```

__Example__

Query `ibc-1` for the acknowledgment of packet with sequence `2` received on `transfer` port and `channel-1`:

```shell
{{#template ../../../templates/commands/hermes/query/packet/ack_1.md CHAIN_ID=ibc-1 PORT_ID=transfer CHANNEL_ID=channel-1 SEQUENCE=2}}
```

```json
Success: "08F7557ED51826FE18D84512BF24EC75001EDBAF2123A477DF72A0A9F3640A7C"
```

## Unreceived Packets

Use the `query packet pending-sends` command to query the sequence numbers of all packets that have been sent on the source chain but not yet received on the destination chain.

```shell
{{#include ../../../templates/help_templates/query/packet/pending-sends.md}}
```

__Example__

Query `transfer` port and `channel-1` on `ibc-1` for the sequence numbers of packets sent on `ibc-0` but not yet received:

```shell
{{#template ../../../templates/commands/hermes/query/packet/pending-sends_1.md CHAIN_ID=ibc-1 PORT_ID=transfer CHANNEL_ID=channel-1}}
```

```json
Success: [
    1,
    2,
    3
]
```

## Unreceived Acknowledgments

Use the `query packet pending-acks` command to query the sequence numbers of all packets that have not yet been acknowledged.

```shell
{{#include ../../../templates/help_templates/query/packet/pending-acks.md}}
```

__Example__

Query `transfer` port and `channel-0` on `ibc-0` for the sequence numbers of packets received by `ibc-1` but not yet acknowledged on `ibc-0`:

```shell
{{#template ../../../templates/commands/hermes/query/packet/pending-acks_1.md CHAIN_ID=ibc-0 PORT_ID=transfer CHANNEL_ID=channel-0}}
```

```json
Success: [
    1,
    2,
    3
]
```

# Packet Queries

Use the `query packet` commands to query information about packets.


```shell
USAGE:
    hermes query packet <SUBCOMMAND>

DESCRIPTION:
    query information about packet(s)

SUBCOMMANDS:
    commitments query packet commitments
    commitment query packet commitment
    acks       query packet acknowledgments
    ack        query packet acknowledgment
    unreceived-packets query unreceived packets
    unreceived-acks query unreceived acknowledgments
```

## Packet Commitments

Use the `query packet commitments` command to query the sequence numbers of all packets that have been sent but not yet acknowledged (these are the packets that still have their commitments stored).

```shell
USAGE:
    hermes query packet commitments <OPTIONS>

DESCRIPTION:
    query packet commitments

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
```

__Example__

Query `ibc-0` for the sequence numbers of packets that still have commitments on `ibc-0` and that were sent on `transfer` port and `channel-0`:

```shell
hermes query packet commitments ibc-0 transfer channel-0 | jq
```

```json
{
  "status": "success",
  "result": {
    "height": {
      "revision_height": 139,
      "revision_number": 0
    },
    "seqs": [
      1,
      2,
      3
    ]
  }
}
```

## Packet Commitment with Sequence

Use the `query packet commitment` command to query the commitment value of a packet with a given sequence number.

```shell
USAGE:
    hermes query packet commitment <OPTIONS>

DESCRIPTION:
    query packet commitment

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
    sequence                  sequence of packet to query

FLAGS:
    -h, --height HEIGHT       height of the state to query
```

__Example__

Query `ibc-0` for the commitment of packet with sequence `3` sent on `transfer` port and `channel-0`:

```shell
hermes query packet commitment ibc-0 transfer channel-0 3 | jq
```

```json
{
  "status": "success",
  "result": "F9458DC7EBEBCD6D18E983FCAB5BD752CC2A74532BBD50B812DB229997739EFC"
}
```

## Packet Acknowledgments

Use the `query packet acknowledgments` command to query the sequence numbers of all packets that have been acknowledged.

```shell
USAGE:
    hermes query packet acks <OPTIONS>

DESCRIPTION:
    query packet acknowledgments

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
```

__Example__

Query `ibc-1` for the sequence numbers of packets acknowledged that were received on `transfer` port and `channel-1`:

```shell
hermes query packet acks ibc-1 transfer channel-1 | jq
```

```json
{
  "status": "success",
  "result": {
    "height": {
      "revision_height": 397,
      "revision_number": 1
    },
    "seqs": [
      1,
      2,
      3
    ]
  }
}
```

## Packet Acknowledgment with Sequence

Use the `query packet acknowledgment` command to query the acknowledgment value of a packet with a given sequence number.

```shell
USAGE:
    hermes query packet ack <OPTIONS>

DESCRIPTION:
    query packet acknowledgment

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query
    sequence                  sequence of packet to query

FLAGS:
    -h, --height HEIGHT       height of the state to query
```

__Example__

Query `ibc-1` for the acknowledgment of packet with sequence `2` received on `transfer` port and `channel-1`:

```shell
hermes query packet ack ibc-1 transfer channel-1 2 | jq
```

```json
{
  "status": "success",
  "result": "08F7557ED51826FE18D84512BF24EC75001EDBAF2123A477DF72A0A9F3640A7C"
}
```

## Unreceived Packets

Use the `query packet unreceived-packets` command to query the sequence numbers of all packets that have been sent on the source chain but not yet received on the destination chain.

```shell
USAGE:
    hermes query packet unreceived-packets <OPTIONS>

DESCRIPTION:
    query unreceived packets

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the chain to query the unreceived sequences
    src_chain_id              identifier of the chain where sent sequences are queried
    src_port_id               identifier of the port to query on source chain
    src_channel_id            identifier of the channel to query on source chain
```

__Example__

Query `ibc-1` for the sequence numbers of packets sent on `ibc-0` on `transfer` port and `channel-0` but not yet received:

```shell
hermes query packet unreceived-packets ibc-1 ibc-0 transfer channel-0 | jq
```

```json
{
  "status": "success",
  "result": [
    1,
    2,
    3
  ]
}
```

## Unreceived Acknowledgments

Use the `query packet unreceived-acks` command to query the sequence numbers of all packets that have been received by the source chain but not yet acknowledged by the destination chain.

```shell
USAGE:
    hermes query packet unreceived-acks <OPTIONS>

DESCRIPTION:
    query unreceived acknowledgments

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the chain to query the unreceived acknowledgments
    src_chain_id              identifier of the chain where received sequences are queried
    src_port_id               identifier of the port to query on source chain
    src_channel_id            identifier of the channel to query on source chain
```

__Example__

Query `ibc-0` for the sequence numbers of packets received on `ibc-1` on `transfer` port and `channel-1` but not yet acknowledged on `ibc-0`:

```shell
hermes query packet unreceived-acks ibc-0 ibc-1 transfer channel-1 | jq
```

```json
{
  "status": "success",
  "result": [
    1,
    2,
    3
  ]
}
```

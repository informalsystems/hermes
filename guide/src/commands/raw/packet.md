# Packet Tx Commands

## Table of Contents

<!-- toc -->

## Fungible token transfer

Use the `tx raw ft-transfer` command to send ICS-20 fungible token transfer packets.
__NOTE:__ This command is mainly used for testing the packet features of the relayer.

```shell
USAGE:
    hermes tx raw ft-transfer <OPTIONS>

DESCRIPTION:
    Send a fungible token transfer test transaction (ICS20 MsgTransfer)

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    src_port_id               identifier of the source port
    src_channel_id            identifier of the source channel
    amount                    amount of coins (samoleans, by default) to send (e.g. `100000`)

FLAGS:
    -o, --timeout-height-offset TIMEOUT-HEIGHT-OFFSET  timeout in number of blocks since current
    -t, --timeout-seconds TIMEOUT-SECONDS              timeout in seconds since current
    -r, --receiver RECEIVER                            receiving account address on the destination chain
    -d, --denom DENOM                                  denomination of the coins to send (default: samoleans)
    -n, --number-msgs NUMBER-MSGS                      number of messages to send
    -k, --key KEY                                      use the given signing key (default: `key_name` config)
```

__Example__

Send two transfer packets from the `transfer` module and `channel-0` of `ibc-0` to `ibc-1`. Each transfer if for `9999` samoleans (default denomination) and a timeout offset of `10` blocks. The transfer fee is paid by the relayer account on `ibc-1`.

```shell
hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 -o 1000 -n 2
```

```json
Success: [
    SendPacket(
        SendPacket {
            height: Height {
                revision: 0,
                height: 431,
            },
            packet: PortId("transfer") ChannelId("channel-0") Sequence(4),
        },
    ),
    SendPacket(
        SendPacket {
            height: Height {
                revision: 0,
                height: 431,
            },
            packet: PortId("transfer") ChannelId("channel-0") Sequence(5),
        },
    ),
]
```

The transfer packets are stored on `ibc-0` and can be relayed.

> To send transfer packets with a custom receiver address use the `--receiver | -r` flag.

```shell
hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 -o 1000 -n 1 -r board:1938586739
```

```json
Success: [
    SendPacket(
        SendPacket {
            height: Height {
                revision: 0,
                height: 546,
            },
            packet: PortId("transfer") ChannelId("channel-0") Sequence(7),
        },
    ),
]
```

## Relay receive and timeout packets

Use the `tx raw packet-recv` command to relay the packets sent but not yet received. If the sent packets have timed out then a timeout packet is sent to the source chain.

```shell
USAGE:
    hermes tx raw packet-recv <OPTIONS>

DESCRIPTION:
    Relay receive or timeout packets

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    src_port_id               identifier of the source port
    src_channel_id            identifier of the source channel
```

__Example__

Send the two transfer packets to the `ibc-1` module bound to the `transfer` port and the `channel-0`'s counterparty.

__NOTE__: The relayer prepends a client update message before the receive messages.

```shell
hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
```

```json
Success: [
    UpdateClient(
        UpdateClient {
            common: Attributes {
                height: Height {
                    revision: 1,
                    height: 439,
                },
                client_id: ClientId(
                    "07-tendermint-1",
                ),
                client_type: Tendermint,
                consensus_height: Height {
                    revision: 0,
                    height: 449,
                },
            },
            header: Some(
                Tendermint(...),
            ),
        },
    ),
    WriteAcknowledgement(
        WriteAcknowledgement {
            height: Height {
                revision: 1,
                height: 439,
            },
            packet: PortId("transfer") ChannelId("channel-0") Sequence(4),
            ack: [
                123,
                34,
                114,
                101,
                115,
                117,
                108,
                116,
                34,
                58,
                34,
                65,
                81,
                61,
                61,
                34,
                125,
            ],
        },
    ),
    WriteAcknowledgement(
        WriteAcknowledgement {
            height: Height {
                revision: 1,
                height: 439,
            },
            packet: PortId("transfer") ChannelId("channel-0") Sequence(5),
            ack: [
                123,
                34,
                114,
                101,
                115,
                117,
                108,
                116,
                34,
                58,
                34,
                65,
                81,
                61,
                61,
                34,
                125,
            ],
        },
    ),
]
```

Both packets have been relayed to `ibc-1` and acknowledged.

## Relay acknowledgment packets

Use the `tx raw packet-ack` command to relay acknowledgments to the original source of the packets.

```shell
USAGE:
    hermes tx raw packet-ack <OPTIONS>

DESCRIPTION:
    Relay acknowledgment packets

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    src_port_id               identifier of the source port
    src_channel_id            identifier of the source channel
```

__Example__

Send the acknowledgments to the `ibc-0` module bound to the `transfer` port and the `channel-1`'s counterparty.

__NOTE__: The relayer prepends a client update message before the acknowledgments.

```shell
hermes tx raw packet-ack ibc-0 ibc-1 transfer channel-1
```

```json
Success: [
    UpdateClient(
        UpdateClient {
            common: Attributes {
                height: Height {
                    revision: 0,
                    height: 495,
                },
                client_id: ClientId(
                    "07-tendermint-0",
                ),
                client_type: Tendermint,
                consensus_height: Height {
                    revision: 1,
                    height: 483,
                },
            },
            header: Some(
                Tendermint(...),
            ),
        },
    ),
    AcknowledgePacket(
        AcknowledgePacket {
            height: Height {
                revision: 0,
                height: 495,
            },
            packet: PortId("transfer") ChannelId("channel-0") Sequence(4),
        },
    ),
    AcknowledgePacket(
        AcknowledgePacket {
            height: Height {
                revision: 0,
                height: 495,
            },
            packet: PortId("transfer") ChannelId("channel-0") Sequence(5),
        },
    ),
]
```

Both acknowledgments have been received on `ibc-0`.

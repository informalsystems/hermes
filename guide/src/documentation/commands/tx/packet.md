# Packet Tx Commands

## Table of Contents

<!-- toc -->

## Fungible token transfer

Use the `tx ft-transfer` command to send ICS-20 fungible token transfer packets.
__NOTE:__ This command is mainly used for testing the packet features of Hermes.

```shell
{{#template ../../../templates/help_templates/tx/ft-transfer.md}}
```

__Example__

Send two transfer packets from the `transfer` module and `channel-0` of `ibc-0` to `ibc-1`. Each transfer if for `9999` `samoleans` (default denomination) and a timeout offset of `10` blocks. The transfer fee is paid by the associated account on `ibc-1`.

```shell
{{#template ../../../templates/commands/hermes/tx/ft-transfer_1.md DST_CHAIN_ID=ibc-1 SRC_CHAIN_ID=ibc-0 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-0 AMOUNT=9999 OPTIONS=--timeout-height-offset 1000 --number-msgs 2}}
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

> To send transfer packets with a custom receiver address use the `--receiver` flag.

```shell
{{#template ../../../templates/commands/hermes/tx/ft-transfer_1.md DST_CHAIN_ID=ibc-1 SRC_CHAIN_ID=ibc-0 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-0 AMOUNT=9999 OPTIONS=--timeout-height-offset 1000 --number-msgs 1 --receiver board:1938586739}}
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

Use the `tx packet-recv` command to relay the packets sent but not yet received. If the packets sent have timed out then a timeout packet is sent to the source chain.

```shell
{{#template ../../../templates/help_templates/tx/packet-recv.md}}
```

__Example__

Send the two transfer packets to the `ibc-1` module bound to the `transfer` port and the `channel-0`'s counterparty.

__NOTE__: Hermes prepends a `Client Update` message before the `Receive` messages.

```shell
{{#template ../../../templates/commands/hermes/tx/packet-recv_1.md DST_CHAIN_ID=ibc-1 SRC_CHAIN_ID=ibc-0 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-0}}
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

Use the `tx packet-ack` command to relay acknowledgments to the original source of the packets.

```shell
{{#template ../../../templates/help_templates/tx/packet-ack.md}}
```

__Example__

Send the acknowledgments to the `ibc-0` module bound to the `transfer` port and the `channel-1`'s counterparty.

__NOTE__: The relayer prepends a client update message before the acknowledgments.

```shell
{{#template ../../../templates/commands/hermes/tx/packet-ack_1.md DST_CHAIN_ID=ibc-0 SRC_CHAIN_ID=ibc-1 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-1}}
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

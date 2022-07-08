# Packet Tx Commands

## Table of Contents

<!-- toc -->

## Fungible token transfer

Use the `tx ft-transfer` command to send ICS-20 fungible token transfer packets.
__NOTE:__ This command is mainly used for testing the packet features of the relayer.

```shell
USAGE:
    hermes tx ft-transfer [OPTIONS] --receiver-chain <RECEIVER_CHAIN_ID> --sender-chain <SENDER_CHAIN_ID> --sender-port <SENDER_PORT_ID> --sender-channel <SENDER_CHANNEL_ID> --amount <AMOUNT>

DESCRIPTION:
    Send a fungible token transfer test transaction (ICS20 MsgTransfer)

OPTIONS:
        --denom <DENOM>
            Denomination of the coins to send [default: samoleans]

        --key-name <KEY_NAME>
            Use the given signing key name (default: `key_name` config)

        --number-msgs <NUMBER_MSGS>
            Number of messages to send

        --receiver <RECEIVER>
            Receiving account address on the destination chain

        --timeout-height-offset <TIMEOUT_HEIGHT_OFFSET>
            Timeout in number of blocks since current [default: 0]

        --timeout-seconds <TIMEOUT_SECONDS>
            Timeout in seconds since current [default: 0]

REQUIRED:
        --amount <AMOUNT>
            Amount of coins (samoleans, by default) to send (e.g. `100000`)

        --receiver-chain <RECEIVER_CHAIN_ID>
            Identifier of the destination chain

        --sender-chain <SENDER_CHAIN_ID>
            Identifier of the source chain

        --sender-channel <SENDER_CHANNEL_ID>
            Identifier of the source channel [aliases: sender-chan]

        --sender-port <SENDER_PORT_ID>
            Identifier of the source port
```

__Example__

Send two transfer packets from the `transfer` module and `channel-0` of `ibc-0` to `ibc-1`. Each transfer if for `9999` samoleans (default denomination) and a timeout offset of `10` blocks. The transfer fee is paid by the relayer account on `ibc-1`.

```shell
hermes tx ft-transfer --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0 --amount 9999 --timeout-height-offset 1000 --number-msgs 2
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
hermes tx ft-transfer --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0 --amount 9999 --timeout-height-offset 1000 --number-msgs 1 --receiver board:1938586739
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

Use the `tx packet-recv` command to relay the packets sent but not yet received. If the sent packets have timed out then a timeout packet is sent to the source chain.

```shell
USAGE:
    hermes tx packet-recv --receiver-chain <RECEIVER_CHAIN_ID> --sender-chain <SENDER_CHAIN_ID> --sender-port <SENDER_PORT_ID> --sender-channel <SENDER_CHANNEL_ID>

DESCRIPTION:
    Relay receive or timeout packets

REQUIRED:
        --receiver-chain <RECEIVER_CHAIN_ID>
            Identifier of the destination chain

        --sender-chain <SENDER_CHAIN_ID>
            Identifier of the source chain

        --sender-channel <SENDER_CHANNEL_ID>
            Identifier of the source channel [aliases: sender-chan]

        --sender-port <SENDER_PORT_ID>
            Identifier of the source port
```

__Example__

Send the two transfer packets to the `ibc-1` module bound to the `transfer` port and the `channel-0`'s counterparty.

__NOTE__: The relayer prepends a client update message before the receive messages.

```shell
hermes tx packet-recv --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0
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
USAGE:
    hermes tx packet-ack --receiver-chain <RECEIVER_CHAIN_ID> --sender-chain <SENDER_CHAIN_ID> --sender-port <SENDER_PORT_ID> --sender-channel <SENDER_CHANNEL_ID>

DESCRIPTION:
    Relay acknowledgment packets

REQUIRED:
        --receiver-chain <RECEIVER_CHAIN_ID>
            Identifier of the destination chain

        --sender-chain <SENDER_CHAIN_ID>
            Identifier of the source chain

        --sender-channel <SENDER_CHANNEL_ID>
            Identifier of the source channel [aliases: sender-chan]

        --sender-port <SENDER_PORT_ID>
            Identifier of the source port
```

__Example__

Send the acknowledgments to the `ibc-0` module bound to the `transfer` port and the `channel-1`'s counterparty.

__NOTE__: The relayer prepends a client update message before the acknowledgments.

```shell
hermes tx packet-ack --receiver-chain ibc-0 --sender-chain ibc-1 --sender-port transfer --sender-channel channel-1
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

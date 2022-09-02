# Packet Tx Commands

## Table of Contents

<!-- toc -->

## Fungible token transfer

Use the `tx ft-transfer` command to send ICS-20 fungible token transfer packets.
__NOTE:__ This command is mainly used for testing the packet features of the relayer.

```shell
USAGE:
    hermes tx ft-transfer [OPTIONS] --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --src-port <SRC_PORT_ID> --src-channel <SRC_CHANNEL_ID> --amount <AMOUNT>

OPTIONS:
        --denom <DENOM>
            Denomination of the coins to send [default: samoleans]

    -h, --help
            Print help information

        --key-name <KEY_NAME>
            Use the given signing key name (default: `key_name` config)

        --number-msgs <NUMBER_MSGS>
            Number of messages to send

        --receiver <RECEIVER>
            The account address on the destination chain which will receive the tokens. If omitted,
            the relayer's wallet on the destination chain will be used

        --timeout-height-offset <TIMEOUT_HEIGHT_OFFSET>
            Timeout in number of blocks since current [default: 0]

        --timeout-seconds <TIMEOUT_SECONDS>
            Timeout in seconds since current [default: 0]

REQUIRED:
        --amount <AMOUNT>
            Amount of coins (samoleans, by default) to send (e.g. `100000`)

        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-channel <SRC_CHANNEL_ID>
            Identifier of the source channel [aliases: src-chan]

        --src-port <SRC_PORT_ID>
            Identifier of the source port
```

__Example__

Send two transfer packets from the `transfer` module and `channel-0` of `ibc-0` to `ibc-1`. Each transfer if for `9999` samoleans (default denomination) and a timeout offset of `10` blocks. The transfer fee is paid by the relayer account on `ibc-1`.

```shell
hermes tx ft-transfer --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-channel channel-0 --amount 9999 --timeout-height-offset 1000 --number-msgs 2
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
hermes tx ft-transfer --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-channel channel-0 --amount 9999 --timeout-height-offset 1000 --number-msgs 1 --receiver board:1938586739
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
USAGE:
    hermes tx packet-recv --reference-chain <REFERENCE_CHAIN_ID> --host-chain <HOST_CHAIN_ID> --host-port <HOST_PORT_ID> --host-channel <HOST_CHANNEL_ID>

DESCRIPTION:
    Relay receive or timeout packets

REQUIRED:
        --reference-chain <REFERENCE_CHAIN_ID>
            Identifier of the destination chain

        --host-chain <HOST_CHAIN_ID>
            Identifier of the source chain

        --host-channel <HOST_CHANNEL_ID>
            Identifier of the source channel [aliases: sender-chan]

        --host-port <HOST_PORT_ID>
            Identifier of the source port
```

__Example__

Send the two transfer packets to the `ibc-1` module bound to the `transfer` port and the `channel-0`'s counterparty.

__NOTE__: The relayer prepends a client update message before the Receive messages.

```shell
hermes tx packet-recv --reference-chain ibc-1 --host-chain ibc-0 --host-port transfer --host-channel channel-0
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
    hermes tx packet-ack --reference-chain <REFERENCE_CHAIN_ID> --host-chain <HOST_CHAIN_ID> --host-port <HOST_PORT_ID> --host-channel <HOST_CHANNEL_ID>

DESCRIPTION:
    Relay acknowledgment packets

REQUIRED:
        --reference-chain <REFERENCE_CHAIN_ID>
            Identifier of the destination chain

        --host-chain <HOST_CHAIN_ID>
            Identifier of the source chain

        --host-channel <HOST_CHANNEL_ID>
            Identifier of the source channel [aliases: sender-chan]

        --host-port <HOST_PORT_ID>
            Identifier of the source port
```

__Example__

Send the acknowledgments to the `ibc-0` module bound to the `transfer` port and the `channel-1`'s counterparty.

__NOTE__: The relayer prepends a client update message before the acknowledgments.

```shell
hermes tx packet-ack --reference-chain ibc-0 --host-chain ibc-1 --host-port transfer --host-channel channel-1
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

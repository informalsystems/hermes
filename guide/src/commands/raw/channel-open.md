# Channel Open Handshake

The `tx` commands can be used to establish a channel for a given connection. Only `unordered` channels are currently supported.

<center>

```mermaid
sequenceDiagram
    autonumber
    participant A as ibc-1
    participant B as ibc-0
    Note over A, B: No channel
    A->>B: ChannelOpenInit
    Note over B: channel: channel-0
    Note over B: channel: counterparty: none
    B->>A: ChannelOpenTry
    Note over A: channel: channel-1
    Note over A: channel: counterparty: channel-0
    A->>B: ChannelOpenAck
    note over B: channel: channel-0
    note over B: counterparty: channel-1
    B->>A: ChannelOpenConfirm
    Note over A, B: Channel open
```

</center>

## Table of Contents

<!-- toc -->

## Channel Open Init

Use the `chan-open-init` command to initialize a new channel.

```shell
USAGE:
    hermes tx chan-open-init [OPTIONS] --b-chain <B_CHAIN_ID> --a-chain <A_CHAIN_ID> --b-connection <B_CONNECTION_ID> --b-port <B_PORT_ID> --a-port <A_PORT_ID>

DESCRIPTION:
    Initialize a channel (ChannelOpenInit)

OPTIONS:
        --order <ORDER>    The channel ordering, valid options 'unordered' (default) and 'ordered'
                           [default: ORDER_UNORDERED]

REQUIRED:
        --a-chain <A_CHAIN_ID>
            Identifier of the source chain

        --a-port <A_PORT_ID>
            Identifier of the source port

        --b-chain <B_CHAIN_ID>
            Identifier of the destination chain

        --b-connection <B_CONNECTION_ID>
            Identifier of the destination connection [aliases: b-conn]

        --b-port <B_PORT_ID>
            Identifier of the destination port
```

__Example__

First, let's initialize the channel on `ibc-0` using an existing connection identified by `connection-0`:

```shell
hermes tx chan-open-init --b-chain ibc-0 --a-chain ibc-1 --b-connection connection-0 --b-port transfer --a-port transfer
```

```json
Success: OpenInitChannel(
    OpenInit(
        Attributes {
            height: Height {
                revision: 0,
                height: 3091
            },
            port_id: PortId(
                "transfer",
            ),
            channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
            connection_id: ConnectionId(
                "connection-0",
            ),
            counterparty_port_id: PortId(
                "transfer",
            ),
            counterparty_channel_id: None,
        },
    ),
)
```

A new channel has been initialized on `ibc-1` with identifier `channel-0`.

> Note that the `counterparty_channel_id` field is currently empty.


## Channel Open Try

Use the `chan-open-try` command to establish a counterparty to the channel on the other chain.

```shell
USAGE:
    hermes tx chan-open-try [OPTIONS] --b-chain <B_CHAIN_ID> --a-chain <A_CHAIN_ID> --b-connection <B_CONNECTION_ID> --b-port <B_PORT_ID> --a-port <A_PORT_ID> --a-channel <A_CHANNEL_ID>

DESCRIPTION:
    Relay the channel attempt (ChannelOpenTry)

OPTIONS:
        --b-channel <B_CHANNEL_ID>    Identifier of the destination channel (optional) [aliases:
                                      b-chan]

REQUIRED:
        --a-chain <A_CHAIN_ID>
            Identifier of the source chain

        --a-channel <A_CHANNEL_ID>
            Identifier of the source channel (required) [aliases: a-chan]

        --a-port <A_PORT_ID>
            Identifier of the source port

        --b-chain <B_CHAIN_ID>
            Identifier of the destination chain

        --b-connection <B_CONNECTION_ID>
            Identifier of the destination connection [aliases: b-conn]

        --b-port <B_PORT_ID>
            Identifier of the destination port
```

__Example__

Let's now create the counterparty to `channel-0` on chain `ibc-1`:

```shell
hermes tx chan-open-try --b-chain ibc-1 --a-chain ibc-0 --b-connection connection-1 --b-port transfer --a-port transfer --a-channel channel-0
```

```json
Success: OpenTryChannel(
    OpenTry(
        Attributes {
            height: Height {
                revision: 1,
                height: 3213
            },
            port_id: PortId(
                "transfer",
            ),
            channel_id: Some(
                ChannelId(
                    "channel-1",
                ),
            ),
            connection_id: ConnectionId(
                "connection-1",
            ),
            counterparty_port_id: PortId(
                "transfer",
            ),
            counterparty_channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
        },
    ),
)
```

A new channel has been created on `ibc-1` with identifier `channel-1`.

> Note that the field `counterparty_channel_id` points to the channel on `ibc-0`.


## Channel Open Ack

Use the `chan-open-ack` command to acknowledge the channel on the initial chain.

```shell
USAGE:
    hermes tx chan-open-ack --b-chain <B_CHAIN_ID> --a-chain <A_CHAIN_ID> --b-connection <B_CONNECTION_ID> --b-port <B_PORT_ID> --a-port <A_PORT_ID> --b-channel <B_CHANNEL_ID> --a-channel <A_CHANNEL_ID>

DESCRIPTION:
    Relay acknowledgment of a channel attempt (ChannelOpenAck)

REQUIRED:
        --a-chain <A_CHAIN_ID>
            Identifier of the source chain

        --a-channel <A_CHANNEL_ID>
            Identifier of the source channel (required) [aliases: a-chan]

        --a-port <A_PORT_ID>
            Identifier of the source port

        --b-chain <B_CHAIN_ID>
            Identifier of the destination chain

        --b-channel <B_CHANNEL_ID>
            Identifier of the destination channel (required) [aliases: b-chan]

        --b-connection <B_CONNECTION_ID>
            Identifier of the destination connection [aliases: b-conn]

        --b-port <B_PORT_ID>
            Identifier of the destination port
```

__Example__

We can now acknowledge on `ibc-0` that `ibc-1` has accepted the opening of the channel:

```shell
hermes tx chan-open-ack --b-chain ibc-0 --a-chain ibc-1 --b-connection connection-0 --b-port transfer --a-port transfer --b-channel channel-0 --a-channel channel-1
```

```json
Success: OpenAckChannel(
    OpenAck(
        Attributes {
            height: Height {
                revision: 0,
                height: 3301
            },
            port_id: PortId(
                "transfer",
            ),
            channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
            connection_id: ConnectionId(
                "connection-0",
            ),
            counterparty_port_id: PortId(
                "transfer",
            ),
            counterparty_channel_id: Some(
                ChannelId(
                    "channel-1",
                ),
            ),
        },
    ),
)
```

> Note that the field `counterparty_channel_id` now points to the channel on `ibc-1`.


## Channel Open Confirm

Use the `chan-open-confirm` command to confirm that the channel has been acknowledged,
and finish the handshake, after which the channel is open on both chains.

```shell
USAGE:
    hermes tx chan-open-confirm --b-chain <B_CHAIN_ID> --a-chain <A_CHAIN_ID> --b-connection <B_CONNECTION_ID> --b-port <B_PORT_ID> --a-port <A_PORT_ID> --b-channel <B_CHANNEL_ID> --a-channel <A_CHANNEL_ID>

DESCRIPTION:
    Confirm opening of a channel (ChannelOpenConfirm)

REQUIRED:
        --a-chain <A_CHAIN_ID>
            Identifier of the source chain

        --a-channel <A_CHANNEL_ID>
            Identifier of the source channel (required) [aliases: a-chan]

        --a-port <A_PORT_ID>
            Identifier of the source port

        --b-chain <B_CHAIN_ID>
            Identifier of the destination chain

        --b-channel <B_CHANNEL_ID>
            Identifier of the destination channel (required) [aliases: b-chan]

        --b-connection <B_CONNECTION_ID>
            Identifier of the destination connection [aliases: b-conn]

        --b-port <B_PORT_ID>
            Identifier of the destination port
```

__Example__

Confirm on `ibc-1` that `ibc-0` has accepted the opening of the channel,
after which the channel is open on both chains.

```shell
hermes tx chan-open-confirm --b-chain ibc-1 --a-chain ibc-0 --b-connection connection-1 --b-port transfer --a-port transfer --b-channel channel-1 --a-channel channel-0
```

```json
    OpenConfirm(
        Attributes {
            height: Height {
                revision: 1,
                height: 3483
            },
            port_id: PortId(
                "transfer",
            ),
            channel_id: Some(
                ChannelId(
                    "channel-1",
                ),
            ),
            connection_id: ConnectionId(
                "connection-1",
            ),
            counterparty_port_id: PortId(
                "transfer",
            ),
            counterparty_channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
        },
    ),
)
```

We have now successfully opened a channel over an existing connection between the two chains.


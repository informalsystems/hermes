# Channel Close Handshake

The channel close handshake involves two steps: init and confirm.

## Table of Contents

<!-- toc -->

## Channel Close Init

Use the `chan-close-init` command to initialize the closure of a channel.

```shell
USAGE:
    hermes tx chan-close-init --b-chain <B_CHAIN_ID> --a-chain <A_CHAIN_ID> --b-connection <B_CONNECTION_ID> --b-port <B_PORT_ID> --a-port <A_PORT_ID> --b-channel <B_CHANNEL_ID> --a-channel <A_CHANNEL_ID>

DESCRIPTION:
    Initiate the closing of a channel (ChannelCloseInit)

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

```shell
hermes tx chan-close-init --b-chain ibc-0 --a-chain ibc-1 --b-connection connection-0 --b-port transfer --a-port transfer --b-channel channel-0 --a-channel channel-1
```

```json
Success: CloseInitChannel(
    CloseInit(
        Attributes {
            height: Height {
                revision: 0,
                height: 77,
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

## Channel Close Confirm

Use the `chan-close-confirm` command to confirm the closure of a channel.

```shell
USAGE:
    hermes tx chan-close-confirm --b-chain <B_CHAIN_ID> --a-chain <A_CHAIN_ID> --b-connection <B_CONNECTION_ID> --b-port <B_PORT_ID> --a-port <A_PORT_ID> --b-channel <B_CHANNEL_ID> --a-channel <A_CHANNEL_ID>

DESCRIPTION:
    Confirm the closing of a channel (ChannelCloseConfirm)

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

```shell
hermes tx chan-close-confirm --b-chain ibc-1 --a-chain ibc-0 --b-connection connection-1 --a-port transfer --b-port transfer --b-channel channel-1 --a-channel channel-0
```

```json
Success: CloseConfirmChannel(
    CloseConfirm(
        Attributes {
            height: Height {
                revision: 1,
                height: 551,
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

__NOTE__: The `cosmos-sdk` transfer module implementation does not allow the user (`hermes` in this case) to initiate the closing of channels.
Therefore, when using the Gaia release image, the `chan-close-init` command
fails as the `MsgChannelCloseInit` message included in the transaction is rejected.
To be able to test channel closure, you need to [patch](../../help.md#patching-gaia) your gaia deployments.

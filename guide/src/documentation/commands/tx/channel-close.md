# Channel Close Handshake

The channel close handshake involves two steps: init and confirm.

## Table of Contents

<!-- toc -->

## Channel Close Init

Use the `chan-close-init` command to initialize the closure of a channel.

```shell
USAGE:
    hermes tx chan-close-init --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --dst-connection <DST_CONNECTION_ID> --dst-port <DST_PORT_ID> --src-port <SRC_PORT_ID> --dst-channel <DST_CHANNEL_ID> --src-channel <SRC_CHANNEL_ID>

DESCRIPTION:
    Initiate the closing of a channel (ChannelCloseInit)

REQUIRED:
        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-channel <SRC_CHANNEL_ID>
            Identifier of the source channel (required) [aliases: src-chan]

        --src-port <SRC_PORT_ID>
            Identifier of the source port

        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --dst-channel <DST_CHANNEL_ID>
            Identifier of the destination channel (required) [aliases: dst-chan]

        --dst-connection <DST_CONNECTION_ID>
            Identifier of the destination connection [aliases: dst-conn]

        --dst-port <DST_PORT_ID>
            Identifier of the destination port
```

__Example__

```shell
hermes tx chan-close-init --dst-chain ibc-0 --src-chain ibc-1 --dst-connection connection-0 --dst-port transfer --src-port transfer --dst-channel channel-0 --src-channel channel-1
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
    hermes tx chan-close-confirm --dst-chain <DST_CHAIN_ID> --src-chain <SRC_CHAIN_ID> --dst-connection <DST_CONNECTION_ID> --dst-port <DST_PORT_ID> --src-port <SRC_PORT_ID> --dst-channel <DST_CHANNEL_ID> --src-channel <SRC_CHANNEL_ID>

DESCRIPTION:
    Confirm the closing of a channel (ChannelCloseConfirm)

REQUIRED:
        --src-chain <SRC_CHAIN_ID>
            Identifier of the source chain

        --src-channel <SRC_CHANNEL_ID>
            Identifier of the source channel (required) [aliases: src-chan]

        --src-port <SRC_PORT_ID>
            Identifier of the source port

        --dst-chain <DST_CHAIN_ID>
            Identifier of the destination chain

        --dst-channel <DST_CHANNEL_ID>
            Identifier of the destination channel (required) [aliases: dst-chan]

        --dst-connection <DST_CONNECTION_ID>
            Identifier of the destination connection [aliases: dst-conn]

        --dst-port <DST_PORT_ID>
            Identifier of the destination port

```

__Example__

```shell
hermes tx chan-close-confirm --dst-chain ibc-1 --src-chain ibc-0 --dst-connection connection-1 --src-port transfer --dst-port transfer --dst-channel channel-1 --src-channel channel-0
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
To be able to test channel closure, you need to [patch](../../../advanced/troubleshooting/patch-gaia.md) your gaia deployments.

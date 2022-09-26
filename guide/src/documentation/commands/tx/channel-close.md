# Channel Close Handshake

The channel close handshake involves two steps: init and confirm.

## Table of Contents

<!-- toc -->

## Channel Close Init

Use the `chan-close-init` command to initialize the closure of a channel.

```shell
{{#include ../../../templates/help_templates/tx/chan-close-init.md}}
```

__Example__

```shell
{{#template ../../../templates/commands/hermes/tx/chan-close-init_1.md DST_CHAIN_ID=ibc-0 SRC_CHAIN_ID=ibc-1 DST_CONNECTION_ID=connection-0 DST_PORT_ID=transfer SRC_PORT_ID=transfer DST_CHANNEL_ID=channel-0 SRC_CHANNEL_ID=channel-1}}
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
{{#include ../../../templates/help_templates/tx/chan-close-confirm.md}}
```

__Example__

```shell
{{#template ../../../templates/commands/hermes/tx/chan-close-confirm_1.md DST_CHAIN_ID=ibc-1 SRC_CHAIN_ID=ibc-0 DST_CONNECTION_ID=connection-1 DST_PORT_ID=transfer SRC_PORT_ID=transfer DST_CHANNEL_ID=channel-1 SRC_CHANNEL_ID=channel-0}}
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

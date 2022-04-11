# Channel

## Table of Contents

<!-- toc -->

## Establish Channel

Use the `create channel` command to establish a new channel.

```shell
USAGE:
    hermes create channel [OPTIONS] --port-a <PORT_A> --port-b <PORT_B> <CHAIN_A> [CONNECTION_A]

DESCRIPTION:
    Create a new channel between two chains using a pre-existing connection.
    Alternatively, create a new client and a new connection underlying the new channel if a pre-existing connection is not provided.

POSITIONAL ARGUMENTS:
    <CHAIN_A>                Identifier of the side `a` chain for the new channel
    <CONNECTION_A>           Identifier of the connection on chain `a` to use in creating the new channel

FLAGS:
    -c, --chain-b <CHAIN_B>         Identifier of the side `b` chain for the new channel
    -h, --help                         Print help information
        --new-client-connection        Indicates that a new client and connection will be created underlying the new channel
    -o, --order <ORDER>                The channel ordering, valid options 'unordered' (default) and 'ordered' [default: ORDER_UNORDERED]
        --port-a <PORT_A>              Identifier of the side `a` port for the new channel
        --port-b <PORT_B>              Identifier of the side `b` port for the new channel
    -v, --channel-version <VERSION>    The version for the new channel
```

## Examples

### New channel over an existing connection

This is the preferred way to create a new channel, by leveraging an existing
connection.

Create a new unordered channel between `ibc-0` and `ibc-1` over an existing connection,
specifically the one we just created in the example above, with port name
`transfer` on both sides:

```shell
hermes create channel ibc-0 --connection-a connection-0 --port-a transfer --port-b transfer -o unordered
```

Notice that one can omit the destination chain parameter, as Hermes will automatically
figure it out by looking up the given connection on `ibc-0`.

```json
🥳  ibc-0 => OpenInitChannel(
    OpenInit(
        Attributes {
            height: Height { revision: 0, height: 129 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-1")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: None
        }
    )
)
🥳  ibc-1 => OpenTryChannel(
    OpenTry(
        Attributes {
            height: Height { revision: 1, height: 126 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-1")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: Some(ChannelId("channel-1"))
        }
    )
)
🥳  ibc-0 => OpenAckChannel(
    OpenAck(
        Attributes {
            height: Height { revision: 0, height: 137 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-1")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: Some(ChannelId("channel-1"))
        }
    )
)
🥳  ibc-1 => OpenConfirmChannel(
    OpenConfirm(
        Attributes {
            height: Height { revision: 1, height: 129 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-1")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: Some(ChannelId("channel-1"))
        }
    )
)
🥳  🥳  🥳  Channel handshake finished for Channel {
    ordering: Unordered,
    a_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-1",
        ),
    },
    b_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-1",
                version: 1,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-1",
        ),
    },
    connection_delay: 0s,
}
Success: Channel {
    ordering: Unordered,
    a_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-1",
        ),
    },
    b_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-1",
                version: 1,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-1",
        ),
    },
    connection_delay: 0s,
}
```

### New channel over a new connection

Should you specifically want to create a new client and a new connection as part
of the `create channel` flow, that option exists, though this is the
less-preferred option over the previous flow, as creating new clients and
connections should only be done in certain specific circumstances so as not to
create redundant resources.

Create a new unordered channel between `ibc-0` and `ibc-1` over a new
connection, using port name `transfer` on both sides and accepting the
interactive prompt that pops up notifying you that a new client and a new
connection will be initialized as part of the process:

```shell
hermes create channel ibc-0 --chain-b ibc-1 --port-a transfer --port-b transfer -o unordered --new-client-connection
```

```json
🥂  ibc-0 => OpenInitConnection(
    OpenInit(
        Attributes {
            height: Height { revision: 0, height: 66 },
            connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-0",
            ),
            counterparty_connection_id: None,
            counterparty_client_id: ClientId(
                "07-tendermint-0",
            ),
        },
    ),
)

🥂  ibc-1 => OpenTryConnection(
    OpenTry(
        Attributes {
            height: Height { revision: 1, height: 64 },
            connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-0",
            ),
            counterparty_connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            counterparty_client_id: ClientId(
                "07-tendermint-0",
            ),
        },
    ),
)

🥂  ibc-0 => OpenAckConnection(
    OpenAck(
        Attributes {
            height: Height { revision: 0, height: 76 },
            connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-0",
            ),
            counterparty_connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            counterparty_client_id: ClientId(
                "07-tendermint-0",
            ),
        },
    ),
)

🥂  ibc-1 => OpenConfirmConnection(
    OpenConfirm(
        Attributes {
            height: Height { revision: 1, height: 68 },
            connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-0",
            ),
            counterparty_connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            counterparty_client_id: ClientId(
                "07-tendermint-0",
            ),
        },
    ),
)

🥂🥂🥂  Connection handshake finished for [Connection {
    delay_period: 0s,
    a_side: ConnectionSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
    },
    b_side: ConnectionSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-1",
                version: 1,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
    },
}]

🥳  ibc-0 => OpenInitChannel(
    OpenInit(
        Attributes {
            height: Height { revision: 0, height: 78 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-0")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: None
        }
    )
)

🥳  ibc-1 => OpenTryChannel(
    OpenTry(
        Attributes {
            height: Height { revision: 1, height: 70 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-0")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: Some(ChannelId("channel-0"))
        }
    )
)

🥳  ibc-0 => OpenAckChannel(
    OpenAck(
        Attributes {
            height: Height { revision: 0, height: 81 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-0")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: Some(ChannelId("channel-0"))
        }
    )
)

🥳  ibc-1 => OpenConfirmChannel
    OpenConfirm
        Attributes {
            height: Height { revision: 1, height: 73 },
            port_id: PortId("transfer"),
            channel_id: Some(ChannelId("channel-0")),
            connection_id: ConnectionId("connection-0"),
            counterparty_port_id: PortId("transfer"),
            counterparty_channel_id: Some(ChannelId("channel-0"))
        }
    )
)

🥳  🥳  🥳  Channel handshake finished for Channel {
    ordering: Unordered,
    a_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-0",
        ),
    },
    b_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-1",
                version: 1,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-0",
        ),
    },
    connection_delay: 0s,
}

Success: Channel {
    ordering: Unordered,
    a_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-0",
        ),
    },
    b_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-1",
                version: 1,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-0",
        ),
    },
    connection_delay: 0s,
}
```

A new channel with identifier `channel-0` on both sides has been established on
a new connection with identifier `connection-0` on both sides.

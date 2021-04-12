# Connection

## Table of Contents

<!-- toc -->

## Establish Connection
Use the `create connection` command to create a new connection.

```shell
USAGE:
    hermes create connection <OPTIONS>

DESCRIPTION:
    Create a new connection between two chains

POSITIONAL ARGUMENTS:
    chain_a_id                identifier of the side `a` chain for the new connection
    chain_b_id                identifier of the side `b` chain for the new connection

FLAGS:
    --client-a CLIENT-A       identifier of client hosted on chain `a`; default: None (creates a new client)
    --client-b CLIENT-B       identifier of client hosted on chain `b`; default: None (creates a new client)

```

__Example__

```shell
hermes create connection ibc-0 ibc-1
```

```rust
🥂  ibc-0 => OpenInitConnection(
    OpenInit(
        Attributes {
            height: revision: 0, height: 4073,
            connection_id: Some(
                ConnectionId(
                    "connection-8",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-8",
            ),
            counterparty_connection_id: None,
            counterparty_client_id: ClientId(
                "07-tendermint-8",
            ),
        },
    ),
)

🥂  ibc-1 => OpenTryConnection(
    OpenTry(
        Attributes {
            height: revision: 1, height: 4069,
            connection_id: Some(
                ConnectionId(
                    "connection-8",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-8",
            ),
            counterparty_connection_id: Some(
                ConnectionId(
                    "connection-8",
                ),
            ),
            counterparty_client_id: ClientId(
                "07-tendermint-8",
            ),
        },
    ),
)

🥂  ibc-0 => OpenAckConnection(
    OpenAck(
        Attributes {
            height: revision: 0, height: 4081,
            connection_id: Some(
                ConnectionId(
                    "connection-8",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-8",
            ),
            counterparty_connection_id: Some(
                ConnectionId(
                    "connection-8",
                ),
            ),
            counterparty_client_id: ClientId(
                "07-tendermint-8",
            ),
        },
    ),
)

🥂  ibc-1 => OpenConfirmConnection(
    OpenConfirm(
        Attributes {
            height: revision: 1, height: 4073,
            connection_id: Some(
                ConnectionId(
                    "connection-8",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-8",
            ),
            counterparty_connection_id: Some(
                ConnectionId(
                    "connection-8",
                ),
            ),
            counterparty_client_id: ClientId(
                "07-tendermint-8",
            ),
        },
    ),
)

🥂🥂🥂  Connection handshake finished for [Connection {
    delay_period: 0ns,
    a_side: ConnectionSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-8",
        ),
        connection_id: ConnectionId(
            "connection-8",
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
            "07-tendermint-8",
        ),
        connection_id: ConnectionId(
            "connection-8",
        ),
    },
}]

Success: Connection {
    delay_period: 0ns,
    a_side: ConnectionSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-8",
        ),
        connection_id: ConnectionId(
            "connection-8",
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
            "07-tendermint-8",
        ),
        connection_id: ConnectionId(
            "connection-8",
        ),
    },
}
```

## Non-zero Delay Connection

A connection can be created with a delay period parameter. This parameter specifies a period of time that must elpase after a successful client state update and before a packet with proofs using its commitment root can pe processed on chain. For more information see [how packet delay works](./packets.html#packet-delay) and  the [connection delay specification](https://github.com/cosmos/ibc/tree/master/spec/core/ics-003-connection-semantics).

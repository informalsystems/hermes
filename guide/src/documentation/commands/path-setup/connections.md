# Connection

## Table of Contents

<!-- toc -->

## Establish Connection
Use the `create connection` command to create a new connection.

```shell
{{#template ../../../templates/help_templates/create/connection.md}}
```

## Examples

### New connection over new clients

Create a new connection between `ibc-0` and `ibc-1` over new clients:

```shell
{{#template ../../../templates/commands/hermes/create/connection_1.md A_CHAIN_ID=ibc-0 B_CHAIN_ID=ibc-1}}
```

```json
🥂  ibc-0 => OpenInitConnection(
    OpenInit(
        Attributes {
            height: Height { revision: 0, height: 4073 },
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
            height: Height { revision: 1, height: 4069 },
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
            height: Height { revision: 0, height: 4081 },
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
            height: Height { revision: 1, height: 4073 },
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

### New connection over existing clients

Create a new connection between `ibc-0` and `ibc-1` over existing clients,
both with client id `07-tendermint-0`:

```shell
{{#template ../../../templates/commands/hermes/create/connection_2.md A_CHAIN_ID=ibc-0 A_CLIENT_ID=07-tendermint-0 B_CLIENT_ID=07-tendermint-0}}
```

Notice that one can omit the destination chain parameter, as Hermes will automatically
figure it out by looking up the given client on `ibc-0`.

## Non-zero Delay Connection

A connection can be created with a delay period parameter. This parameter specifies a period of time that must elpase after a successful client state update and before a packet with proofs using its commitment root can pe processed on chain. For more information see [how packet delay works](../relaying/index.md#packet-delay) and the [connection delay specification](https://github.com/cosmos/ibc/tree/master/spec/core/ics-003-connection-semantics).

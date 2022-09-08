# Relayer Listen Mode

The relayer can be started in `listen` mode to display the events emitted by a given chain. `NewBlock` and `Tx` IBC events are shown.

```shell
USAGE:
    hermes listen [OPTIONS] --chain <CHAIN_ID>

DESCRIPTION:
    Listen to and display IBC events emitted by a chain

OPTIONS:
        --events <EVENT>...    Add an event type to listen for, can be repeated. Listen for all
                               events by default (available: Tx, NewBlock)

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain to listen for events from
```

__Example__

Start the relayer in listen mode for all `ibc-0` events and observe the output:

```shell
hermes listen --chain ibc-0
```

```json
EventBatch {
    chain_id: ChainId {
        id: "ibc-0",
        version: 0,
    },
    height: block::Height(10914),
    events: [
        NewBlock(
            NewBlock {
                height: block::Height(10914),
            },
        ),
    ],
}
EventBatch {
    chain_id: ChainId {
        id: "ibc-0",
        version: 0,
    },
    height: block::Height(10915),
    events: [
        OpenInitConnection(
            OpenInit(
                Attributes {
                    height: block::Height(10915),
                    connection_id: Some(
                        ConnectionId(
                            "connection-3",
                        ),
                    ),
                    client_id: ClientId(
                        "07-tendermint-3",
                    ),
                    counterparty_connection_id: None,
                    counterparty_client_id: ClientId(
                        "07-tendermint-5",
                    ),
                },
            ),
        ),
    ],

...

EventBatch {
    chain_id: ChainId {
        id: "ibc-0",
        version: 0,
    },
    height: block::Height(10919),
    events: [
        UpdateClient(
            UpdateClient(
                Attributes {
                    height: block::Height(10919),
                    client_id: ClientId(
                        "07-tendermint-3",
                    ),
                    client_type: Tendermint,
                    consensus_height: Height {
                        revision: 1,
                        height: 10907,
                    },
                },
            ),
        ),
    ],
}

...

EventBatch {
    chain_id: ChainId {
        id: "ibc-0",
        version: 0,
    },
    height: block::Height(10924),
    events: [
        UpdateClient(
            UpdateClient(
                Attributes {
                    height: block::Height(10924),
                    client_id: ClientId(
                        "07-tendermint-3",
                    ),
                    client_type: Tendermint,
                    consensus_height: Height {
                        revision: 1,
                        height: 10912,
                    },
                },
            ),
        ),
        OpenAckConnection(
            OpenAck(
                Attributes {
                    height: block::Height(10924),
                    connection_id: Some(
                        ConnectionId(
                            "connection-3",
                        ),
                    ),
                    client_id: ClientId(
                        "07-tendermint-3",
                    ),
                    counterparty_connection_id: Some(
                        ConnectionId(
                            "connection-5",
                        ),
                    ),
                    counterparty_client_id: ClientId(
                        "07-tendermint-5",
                    ),
                },
            ),
        ),
    ],
}
```

## Filter events

The `listen` command accepts a `--event` flag to specify which event types to listen for.

At the moment, two event types are available:
- `NewBlock` 
- `Tx`

The `--event` flag can be repeated to specify more than one event type.

- To listen for only `NewBlock` events on `ibc-0`, invoke `hermes listen --chain ibc-0 --events NewBlock`
- To listen for only `Tx` events on `ibc-0`, invoke `hermes listen --chain ibc-0 --events Tx`
- To listen for both `NewBlock` and `Tx` events on `ibc-0`, invoke `hermes listen --chain ibc-0 --events NewBlock Tx`

If the `--event` flag is omitted, the relayer will subscribe to all event types.

# Listen Mode

Hermes can be started in `listen` mode to display the events emitted by a given chain. `NewBlock` and `Tx` IBC events are shown.

```shell
{{#include ../../../templates/help_templates/listen.md}}
```

__Example__

Start Hermes in listen mode for all `ibc-0` events and observe the output:

```shell
{{#template ../../../templates/commands/hermes/listen_1.md CHAIN_ID=ibc-0}}
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

The `listen` command accepts a `--events` flag to specify which event types to listen for.

At the moment, two event types are available:
- `NewBlock` 
- `Tx`

The `--events` flag can be repeated to specify more than one event type.

- To listen for only `NewBlock` events on `ibc-0`, invoke `{{#template ../../../templates/commands/hermes/listen_1.md CHAIN_ID=ibc-0 OPTIONS= --events NewBlock}}`
- To listen for only `Tx` events on `ibc-0`, invoke `{{#template ../../../templates/commands/hermes/listen_1.md CHAIN_ID=ibc-0 OPTIONS= --events Tx}}`
- To listen for both `NewBlock` and `Tx` events on `ibc-0`, invoke `{{#template ../../../templates/commands/hermes/listen_1.md CHAIN_ID=ibc-0 OPTIONS= --events NewBlock Tx}}`

If the `--events` flag is omitted, Hermes will subscribe to all event types.

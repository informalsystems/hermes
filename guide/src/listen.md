# Relayer Listen Mode

The relayer can be started in `listen` mode to display the events emitted by a given chain. `NewBlock` and IBC events are shown.

```shell
USAGE:
    hermes listen <OPTIONS>

DESCRIPTION:
    Listen to IBC events

POSITIONAL ARGUMENTS:
    chain_id
```

__Example__

Start the relayer in listen mode for `ibc-0` events and observe the output:

```shell
hermes listen ibc-0

[relayer-cli/src/commands/listen.rs:45] event_batch = EventBatch {
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
[relayer-cli/src/commands/listen.rs:45] event_batch = EventBatch {
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
[relayer-cli/src/commands/listen.rs:45] event_batch = EventBatch {
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
                        revision_number: 1,
                        revision_height: 10907,
                    },
                },
            ),
        ),
    ],
}
...
[relayer-cli/src/commands/listen.rs:45] event_batch = EventBatch {
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
                        revision_number: 1,
                        revision_height: 10912,
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


# Table of Contents

<!-- toc -->

# Query Clients

Use the `query clients` command to query the identifiers of all clients on a given chain, called
the _host_ chain.

```shell
{{#include ../../../templates/help_templates/query/clients.md}}
```

__Example__

Query all clients on `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/query/clients_1.md HOST_CHAIN_ID=ibc-1}}
```

```json
Success: [
    ClientChain {
        client_id: ClientId(
            "07-tendermint-0",
        ),
        chain_id: ChainId {
            id: "ibc-0",
            version: 0,
        },
    },
    ClientChain {
        client_id: ClientId(
            "07-tendermint-1",
        ),
        chain_id: ChainId {
            id: "ibc-2",
            version: 2,
        },
    },
]
```

Query all clients on `ibc-1` having `ibc-2` as their reference chain:

```shell
{{#template ../../../templates/commands/hermes/query/clients_1.md HOST_CHAIN_ID=ibc-1 OPTIONS= --reference-chain ibc-2}}
```

```json
Success: [
    ClientId(
        "07-tendermint-1",
    ),
]
```

# Query Client Data

Use the `query client` command to query the information about a specific client.

```shell
{{#include ../../../templates/help_templates/query/client.md}}
```

## Query the client state

Use the `query client state` command to query the client state of a client:

```shell
{{#include ../../../templates/help_templates/query/client/state.md}}
```

__Example__

Query the state of client `07-tendermint-2` on `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/query/client/state_1.md CHAIN_ID=ibc-1 CLIENT_ID=07-tendermint-1}}
```

```json
Success: ClientState {
    chain_id: ChainId {
        id: "ibc-2",
        version: 2,
    },
    trust_threshold: TrustThresholdFraction {
        numerator: 1,
        denominator: 3,
    },
    trusting_period: 1209600s,
    unbonding_period: 1814400s,
    max_clock_drift: 3s,
    frozen_height: Height {
        revision: 0,
        height: 0,
    },
    latest_height: Height {
        revision: 2,
        height: 3069,
    },
    upgrade_path: [
        "upgrade",
        "upgradedIBCState",
    ],
    allow_update_after_expiry: true,
    allow_update_after_misbehaviour: true,
}
```

## Query the client consensus state

Use the `query client consensus` command to query the consensus states of a given client, or the state at a specified height:

```shell
{{#include ../../../templates/help_templates/query/client/consensus.md}}
```

__Example__

Query the states of client `07-tendermint-0` on `ibc-0`:

```shell
{{#template ../../../templates/commands/hermes/query/client/consensus_1.md CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-0}}
```

```json
Success: [
    Height {
        revision: 1,
        height: 3049,
    },
    Height {
        revision: 1,
        height: 2888,
    },
    Height {
        revision: 1,
        height: 2736,
    },
    Height {
        revision: 1,
        height: 2729,
    },
    Height {
        revision: 1,
        height: 2724,
    },
    Height {
        revision: 1,
        height: 2717,
    },
]
```

Query `ibc-0` at height `2800` for the consensus state for height `2724`:

```shell
{{#template ../../../templates/commands/hermes/query/client/consensus_1.md CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-0 OPTIONS= --consensus-height 2724 --height 2800}}
```

```json
Success: ConsensusState {
    timestamp: Time(
        2021-04-13T14:11:20.969154Z
    ),
    root: CommitmentRoot(
        "371DD19003221B60162D42C78FD86ABF95A572F3D9497084584B75F97B05B70C"
    ),
    next_validators_hash: Hash::Sha256(
        740950668B6705A136D041914FC219045B1D0AD1C6A284C626BF5116005A98A7
    ),
}
```

## Query the identifiers of all connections associated with a given client

Use the `query client connections` command to query the connections associated with a given client:

```shell
{{#include ../../../templates/help_templates/query/client/connections.md}}
```

__Example__

Query the connections of client `07-tendermint-0` on `ibc-0`:

```shell
{{#template ../../../templates/commands/hermes/query/client/connections_1.md CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-0}}
```

```json
Success: [
    ConnectionId("connection-0"),
    ConnectionId("connection-1"),
]
```

## Query for the header used in a client update at a certain height

```
{{#include ../../../templates/help_templates/query/client/header.md}}
```

__Example__

Query for the header used in the `07-tendermint-0` client update at height 2724 on `ibc-0`:

```shell
{{#template ../../../templates/commands/hermes/query/client/header_1.md CHAIN_ID=ibc-0 CLIENT_ID=07-tendermint-0 CONSENSUS_HEIGHT=2724}}
```

```json
Success: [
    UpdateClient(
        UpdateClient {
            common: Attributes {
                height: Height {
                    revision: 0,
                    height: 0,
                },
                client_id: ClientId(
                    "07-tendermint-0",
                ),
                client_type: Tendermint,
                consensus_height: Height {
                    revision: 1,
                    height: 2724,
                },
            },
            header: Some(
                Tendermint(...),
            ),
        },
    ),
]
```

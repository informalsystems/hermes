
# Table of Contents

<!-- toc -->

# Query Clients

Use the `query clients` command to query the identifiers of all clients on a given chain.

```shell
USAGE:
    hermes query clients <OPTIONS>

DESCRIPTION:
    Query the identifiers of all clients on a chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query

FLAGS:
    -s, --src-chain-id ID     filter for clients which target a specific chain id (implies '-o')
    -o, --omit-chain-ids      omit printing the source chain for each client (default: false)
```

__Example__

Query all clients on `ibc-1`:

```shell
hermes query clients ibc-1
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

Query all clients on `ibc-1` having `ibc-2` as their source chain:

```shell
hermes query clients ibc-1 -s ibc-2
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
USAGE:
    hermes query client <SUBCOMMAND>

DESCRIPTION:
    Query information about clients

SUBCOMMANDS:
    state      query client full state
    consensus  query client consensus
    connections query client connections
```

## Query the client state

Use the `query client state` command to query the client state of a client:

```shell
USAGE:
    hermes query client state <OPTIONS>

DESCRIPTION:
    Query client full state

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    client_id                 identifier of the client to query

FLAGS:
    -H, --height HEIGHT       the chain height which this query should reflect
```

__Example__

Query the state of client `07-tendermint-2` on `ibc-1`:

```shell
hermes query client state ibc-1 07-tendermint-1
```

```json
Success: ClientState {
    chain_id: ChainId {
        id: "ibc-2",
        version: 2,
    },
    trust_level: TrustThresholdFraction {
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
USAGE:
    hermes query client consensus <OPTIONS>

DESCRIPTION:
    Query client consensus state

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    client_id                 identifier of the client to query

FLAGS:
    -c, --consensus-height    CONSENSUS-HEIGHT
    -s, --heights-only        show only consensus heights
    -H, --height HEIGHT       the chain height context to be used, applicable only to a specific height
```

__Example__

Query the states of client `07-tendermint-0` on `ibc-0`:

```shell
hermes query client consensus ibc-0 07-tendermint-0 --heights-only
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
hermes query client consensus ibc-0 07-tendermint-0 -c 2724 -h 2800
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
USAGE:
    hermes query client connections <OPTIONS>

DESCRIPTION:
    Query client connections

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    client_id                 identifier of the client to query

FLAGS:
    -H, --height HEIGHT       the chain height which this query should reflect
```

__Example__

Query the connections of client `07-tendermint-0` on `ibc-0`:

```shell
hermes query client connections ibc-0 07-tendermint-0
```

```json
Success: [
    ConnectionId("connection-0"),
    ConnectionId("connection-1"),
]
```

## Query for the header used in a client update at a certain height

```
USAGE:
    hermes query client header <OPTIONS>

DESCRIPTION:
    Query for the header used in a client update at a certain height

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    client_id                 identifier of the client to query
    consensus_height          height of header to query

FLAGS:
    -H, --height HEIGHT       the chain height context for the query
```

__Example__

Query for the header used in the `07-tendermint-0` client update at height 2724 on `ibc-0`:

```shell
hermes query client header ibc-0 07-tendermint-0 2724
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

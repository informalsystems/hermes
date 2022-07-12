
# Table of Contents

<!-- toc -->

# Query Clients

Use the `query clients` command to query the identifiers of all clients on a given chain, called
the _host_ chain.

```shell
USAGE:
    hermes query clients [OPTIONS] --host-chain <HOST_CHAIN_ID>

DESCRIPTION:
    Query the identifiers of all clients on a chain

OPTIONS:
        --omit-chain-ids
            Omit printing the reference (or target) chain for each client

        --reference-chain <REFERENCE_CHAIN_ID>
            Filter for clients which target a specific chain id (implies '--omit-chain-ids')

REQUIRED:
        --host-chain <HOST_CHAIN_ID>    Identifier of the chain to query
```

__Example__

Query all clients on `ibc-1`:

```shell
hermes query clients --host-chain ibc-1
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
hermes query clients --host-chain ibc-1 --reference-chain ibc-2
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
    connections    Query the client connections
    consensus      Query the client consensus state
    header         Query for the header used in a client update at a certain height
    state          Query the client full state
```

## Query the client state

Use the `query client state` command to query the client state of a client:

```shell
USAGE:
    hermes query client state [OPTIONS] --chain <CHAIN_ID> --client <CLIENT_ID>

DESCRIPTION:
    Query the client state

OPTIONS:
        --height <HEIGHT>    The chain height context for the query

REQUIRED:
        --chain <CHAIN_ID>      Identifier of the chain to query
        --client <CLIENT_ID>    Identifier of the client to query
```

__Example__

Query the state of client `07-tendermint-2` on `ibc-1`:

```shell
hermes query client state --chain ibc-1 --client 07-tendermint-1
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
    hermes query client consensus [OPTIONS] --chain <CHAIN_ID> --client <CLIENT_ID>

DESCRIPTION:
    Query client consensus state

OPTIONS:
        --consensus-height <CONSENSUS_HEIGHT>
            Height of the client's consensus state to query

        --height <HEIGHT>
            The chain height context to be used, applicable only to a specific height

        --heights-only
            Show only consensus heights

REQUIRED:
        --chain <CHAIN_ID>      Identifier of the chain to query
        --client <CLIENT_ID>    Identifier of the client to query
```

__Example__

Query the states of client `07-tendermint-0` on `ibc-0`:

```shell
hermes query client consensus --chain ibc-0 --client 07-tendermint-0 --heights-only
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
hermes query client consensus --chain ibc-0 --client 07-tendermint-0 --consensus-height 2724 --height 2800
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
    hermes query client connections [OPTIONS] --chain <CHAIN_ID> --client <CLIENT_ID>

DESCRIPTION:
    Query client connections

OPTIONS:
        --height <HEIGHT>    The chain height which this query should reflect

REQUIRED:
        --chain <CHAIN_ID>      Identifier of the chain to query
        --client <CLIENT_ID>    Identifier of the client to query
```

__Example__

Query the connections of client `07-tendermint-0` on `ibc-0`:

```shell
hermes query client connections --chain ibc-0 --client 07-tendermint-0
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
    hermes query client header [OPTIONS] --chain <CHAIN_ID> --client <CLIENT_ID> --consensus-height <CONSENSUS_HEIGHT>

DESCRIPTION:
    Query for the header used in a client update at a certain height

OPTIONS:
        --height <HEIGHT>    The chain height context for the query. Leave unspecified for latest
                             height.

REQUIRED:
        --chain <CHAIN_ID>                       Identifier of the chain to query
        --client <CLIENT_ID>                     Identifier of the client to query
        --consensus-height <CONSENSUS_HEIGHT>    Height of header to query
```

__Example__

Query for the header used in the `07-tendermint-0` client update at height 2724 on `ibc-0`:

```shell
hermes query client header --chain ibc-0 --client 07-tendermint-0 --consensus-height 2724
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

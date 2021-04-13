
# Table of Contents

<!-- toc -->

# Query Clients
Use the `query clients` command to query the identifiers of all clients on a given chain.

```shell
USAGE:
    hermes query clients <OPTIONS>

DESCRIPTION:
    Query clients

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
```

__Example__

Query all clients on `ibc-1`:

```shell
hermes query clients ibc-1 | jq
```

```json
{
  "status": "success",
  "result": [
    "07-tendermint-0",
    "07-tendermint-1",
    "07-tendermint-2",
    "07-tendermint-3"
  ]
}
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
    -h, --height HEIGHT       the chain height which this query should reflect
```

__Example__

Query the state of client `07-tendermint-2` on `ibc-1`:

```shell
hermes query client state ibc-1 07-tendermint-2 | jq
```

```json
{
  "status": "success",
  "result": {
    "type": "Tendermint",
    "allow_update_after_expiry": false,
    "allow_update_after_misbehaviour": false,
    "chain_id": "ibc-0",
    "frozen_height": {
      "revision_height": 0,
      "revision_number": 0
    },
    "latest_height": {
      "revision_height": 948,
      "revision_number": 0
    },
    "max_clock_drift": {
      "nanos": 0,
      "secs": 3
    },
    "trust_level": {
      "denominator": "3",
      "numerator": "1"
    },
    "trusting_period": {
      "nanos": 0,
      "secs": 1209600
    },
    "unbonding_period": {
      "nanos": 0,
      "secs": 1814400
    },
    "upgrade_path": [
      "upgrade",
      "upgradedIBCState"
    ]
  }
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
    -h, --height HEIGHT       the chain height context to be used, applicable only to a specific height
```

__Example__

Query the states of client `07-tendermint-0` on `ibc-0`:

```shell
hermes query client consensus ibc-0 07-tendermint-0 -s | jq
```

```json
{
  "result": [
    {
      "revision_height": 169,
      "revision_number": 1
    },
    {
      "revision_height": 164,
      "revision_number": 1
    },
    {
      "revision_height": 139,
      "revision_number": 1
    },
    {
      "revision_height": 137,
      "revision_number": 1
    }
  ],
  "status": "success"
}
```

Query `ibc-0` at height `200` for the consensus state for height `181`:
```shell
hermes query client consensus ibc-0 07-tendermint-0 -c 181 -h 200 | jq
```
```json
{
  "result": {
    "next_validators_hash": "D27C11A760010565B8DC01C4589CE3207AE784F40190F33422A80984A887A8F5",
    "root": "0C17DEF5D5DF5B4B6D91D714E12B4792C0D322CEA9C8C4692AC3FE2F015E9591",
    "timestamp": "2021-04-11T15:39:34.919129Z"
  },
  "status": "success"
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
    -h, --height HEIGHT       the chain height which this query should reflect
```

__Example__

Query the connections of client `07-tendermint-0` on `ibc-0`:

```shell
hermes query client connections ibc-0 07-terndermint-0
{
  "status": "success",
  "result": [
    "connection-0",
    "connection-1",
    "connection-2"
  ]
}```

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
    -p, --proof PROOF         whether proof is required; default: false (no proof)
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
Use the `query client consensus` command to query the consensus state for a given client and consensus height:

```shell
USAGE:
    hermes query client consensus <OPTIONS>

DESCRIPTION:
    Query client consensus state

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    client_id                 identifier of the client to query
    consensus_epoch           epoch of the client's consensus state to query
    consensus_height          height of the client's consensus state to query

FLAGS:
    -h, --height HEIGHT       the chain height which this query should reflect
    -p, --proof PROOF         whether proof is required
```

__Example__

Query the state of client `07-tendermint-2` on `ibc-1`:

```shell
hermes query client consensus ibc-1 07-tendermint-2 0 948 | jq
```

```json
{
  "status": "success",
  "result": {
    "type": "Tendermint",
    "next_validators_hash": "61B504627364047439A253FFBDD5D384B31D29611BD4B2ABA2636C232ABADA33",
    "root": "82EFC9F24C8B595BDADBFE1576B473648DD8EBC76F30DC21201539FCCE15A9F8",
    "timestamp": "2021-02-01T13:42:30.30536Z"
  }
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

# Query Connections

Use the `query connections` command to query the identifiers of all connections on a given chain.

```shell
USAGE:
    hermes query connections <OPTIONS>

DESCRIPTION:
    Query the identifiers of all connections on a chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
```

__Example__

Query all connections on `ibc-1`:

```shell
hermes query connections ibc-1 | jq
```

```json
{
  "status": "success",
  "result": [
    "connection-0",
    "connection-1",
    "connection-2",
    "connection-3"
  ]
}
```

# Query Connection Data

Use the `query connection` commands to query a specific connection.

```shell
USAGE:
    hermes query connection <SUBCOMMAND>

DESCRIPTION:
    Query information about connection(s)

SUBCOMMANDS:
    end        query connection end
    channels   query connection channels
```

## Query the connection end data

Use the `query connection end` command to query the connection end:

```shell
USAGE:
    hermes query connection end <OPTIONS>

DESCRIPTION:
    query connection end

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    connection_id             identifier of the connection to query

FLAGS:
    -h, --height HEIGHT       height of the state to query
    -p, --proof PROOF         whether proof is required; default: false (no proof)
```

__Example__

Query the connection end of connection `connection-1` on `ibc-1`:

```shell
hermes query connection end ibc-1 connection-1 | jq
```

```json
{
  "status": "success",
  "result": {
    "client_id": "07-tendermint-2",
    "counterparty": {
      "client_id": "07-tendermint-1",
      "connection_id": "connection-0",
      "prefix": "ibc"
    },
    "delay_period": 0,
    "state": "Open",
    "versions": [
      {
        "features": [
          "ORDER_ORDERED",
          "ORDER_UNORDERED"
        ],
        "identifier": "1"
      }
    ]
  }
}
```

## Query the identifiers of all channels associated with a given connection

Use the `query connection channels` command to query the identifiers of the channels associated with a given connection:

```shell
USAGE:
    hermes query connection channels <OPTIONS>

DESCRIPTION:
    query connection channels

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    connection_id             identifier of the connection to query
```

__Example__

Query the channels associated with connection `connection-1` on `ibc-1`:

```shell
hermes query connection channels ibc-1 connection-1 | jq
```

```json
{
  "status": "success",
  "result": [
    "channel-1"
  ]
}
```


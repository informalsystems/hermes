# Table of Contents

<!-- toc -->

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
hermes query connections ibc-1
```

```json
Success: [
    ConnectionId(
        "connection-0",
    ),
    ConnectionId(
        "connection-1",
    ),
]
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
```

__Example__

Query the connection end of connection `connection-1` on `ibc-1`:

```shell
hermes query connection end ibc-1 connection-1
```

```json
Success: ConnectionEnd {
    state: Open,
    client_id: ClientId(
        "07-tendermint-1",
    ),
    counterparty: Counterparty {
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: Some(
            ConnectionId(
                "connection-0",
            ),
        ),
        prefix: ibc,
    },
    versions: [
        Version {
            identifier: "1",
            features: [
                "ORDER_ORDERED",
                "ORDER_UNORDERED",
            ],
        },
    ],
    delay_period: 0s,
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
hermes query connection channels ibc-1 connection-1
```

```json
Success: [
    PortChannelId {
        channel_id: ChannelId(
            "channel-0",
        ),
        port_id: PortId(
            "transfer",
        ),
    },
    PortChannelId {
        channel_id: ChannelId(
            "channel-1",
        ),
        port_id: PortId(
            "transfer",
        ),
    },
]
```

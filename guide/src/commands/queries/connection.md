# Table of Contents

<!-- toc -->

# Query Connections

Use the `query connections` command to query the identifiers of all connections on a given chain.

```shell
USAGE:
    hermes query connections --chain <CHAIN_ID>

DESCRIPTION:
    Query the identifiers of all connections on a chain

OPTIONS:
        --counterparty-chain <COUNTERPARTY_CHAIN_ID>
            Filter the query response by the counterparty chain

        --verbose
            Enable verbose output, displaying the client for each connection in the response

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain to query
```

__Example__

Query all connections on `ibc-1`:

```shell
hermes query connections --chain ibc-1
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
    hermes query connection end [OPTIONS] --chain <CHAIN_ID> --connection <CONNECTION_ID>

DESCRIPTION:
    Query connection end

OPTIONS:
        --height <HEIGHT>    Height of the state to query. Leave unspecified for latest height.

REQUIRED:
        --chain <CHAIN_ID>              Identifier of the chain to query
        --connection <CONNECTION_ID>    Identifier of the connection to query [aliases: conn]
```

__Example__

Query the connection end of connection `connection-1` on `ibc-1`:

```shell
hermes query connection end --chain ibc-1 --connection connection-1
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
    hermes query connection channels --chain <CHAIN_ID> --connection <CONNECTION_ID>

DESCRIPTION:
    Query connection channels

REQUIRED:
        --chain <CHAIN_ID>              Identifier of the chain to query
        --connection <CONNECTION_ID>    Identifier of the connection to query [aliases: conn]
```

__Example__

Query the channels associated with connection `connection-1` on `ibc-1`:

```shell
hermes query connection channels --chain ibc-1 --connection connection-1
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

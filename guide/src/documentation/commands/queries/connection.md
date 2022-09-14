# Table of Contents

<!-- toc -->

# Query Connections

Use the `query connections` command to query the identifiers of all connections on a given chain.

```shell
{{#include ../../../templates/help_templates/query/connections.md}}
```

__Example__

Query all connections on `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/query/connections_1.md CHAIN_ID=ibc-1}}
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
{{#include ../../../templates/help_templates/query/connection.md}}
```

## Query the connection end data

Use the `query connection end` command to query the connection end:

```shell
{{#include ../../../templates/help_templates/query/connection/end.md}}
```

__Example__

Query the connection end of connection `connection-1` on `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/query/connection/end_1.md CHAIN_ID=ibc-1 CONNECTION_ID=connection-1}}
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
{{#include ../../../templates/help_templates/query/connection/channels.md}}
```

__Example__

Query the channels associated with connection `connection-1` on `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/query/connection/channels_1.md CHAIN_ID=ibc-1 CONNECTION_ID=connection-1}}
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

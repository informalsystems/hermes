# Table of Contents

<!-- toc -->

# Query Channels

Use the `query channels` command to query the identifiers of all channels on a given chain.

```shell
USAGE:
    hermes query channels <OPTIONS>

DESCRIPTION:
    Query the identifiers of all channels on a given chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
```

__Example__

Query all channels on `ibc-1`:

```shell
hermes query channels ibc-1
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

# Query Channel Data

Use the `query channel` commands to query the information about a specific channel.

```shell
USAGE:
    hermes query channel <SUBCOMMAND>

DESCRIPTION:
    Query information about channels

SUBCOMMANDS:
    end        Query channel end
    ends       Query channel ends and underlying connection and client objects
```

## Query the channel end data

Use the `query channel end` command to query the channel end:

```shell
USAGE:
    hermes query channel end <OPTIONS>

DESCRIPTION:
    Query channel end

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query

FLAGS:
    -h, --height HEIGHT       height of the state to query
```

__Example__

Query the channel end of channel `channel-1` on port `transfer` on `ibc-1`:

```shell
hermes query channel end ibc-1 transfer channel-1
```

```json
Success: ChannelEnd {
    state: Open,
    ordering: Unordered,
    remote: Counterparty {
        port_id: PortId(
            "transfer",
        ),
        channel_id: Some(
            ChannelId(
                "channel-0",
            ),
        ),
    },
    connection_hops: [
        ConnectionId(
            "connection-1",
        ),
    ],
    version: "ics20-1",
}
```

## Query the channel data for both ends of a channel


Use the `query channel ends` command to obtain both ends of a channel:

```shell
USAGE:
    hermes query channel ends <OPTIONS>

DESCRIPTION:
    Query channel ends and underlying connection and client objects

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query

FLAGS:
    -h, --height HEIGHT       height of the state to query
    -v, --verbose             enable verbose output, displaying all details of channels, connections & clients
```

__Example__

Query the channel end of channel `channel-1` on port `transfer` on `ibc-0`:

```shell
hermes query channel ends ibc-0 transfer channel-1
```

```json
Success: ChannelEndsSummary {
    chain_id: ChainId {
        id: "ibc-0",
        version: 0,
    },
    client_id: ClientId(
        "07-tendermint-1",
    ),
    connection_id: ConnectionId(
        "connection-1",
    ),
    channel_id: ChannelId(
        "channel-1",
    ),
    port_id: PortId(
        "transfer",
    ),
    counterparty_chain_id: ChainId {
        id: "ibc-2",
        version: 2,
    },
    counterparty_client_id: ClientId(
        "07-tendermint-1",
    ),
    counterparty_connection_id: ConnectionId(
        "connection-1",
    ),
    counterparty_channel_id: ChannelId(
        "channel-1",
    ),
    counterparty_port_id: PortId(
        "transfer",
    ),
}
```

Passing the `-v` flag will additionally print all the details of the
channel, connection, and client on both ends.
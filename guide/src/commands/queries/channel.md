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
    end        query channel end
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

# Query Channels

Use the `query channels` command to query the identifiers of all channels on a given chain.

```shell
USAGE:
    hermes query channels <OPTIONS>

DESCRIPTION:
    query the identifiers of all channels on a chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
```

__Example__

Query all channels on `ibc-1`:

```shell
$ hermes query channels ibc-1 | jq
```

```json
{
  "status": "success",
  "result": [
    "channel-0",
    "channel-1",
    "channel-2",
    "channel-3"
  ]
}
```

# Query Channel Data

Use the `query channel` commands to query the information about a specific channel.

```shell
USAGE:
    hermes query channel <SUBCOMMAND>

DESCRIPTION:
    query information about channel(s)

SUBCOMMANDS:
    end        query channel end
```

## Query the channel end data

Use the `query channel end` command to query the channel end:

```shell
USAGE:
    hermes query channel end <OPTIONS>

DESCRIPTION:
    query channel end

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    port_id                   identifier of the port to query
    channel_id                identifier of the channel to query

FLAGS:
    -h, --height HEIGHT       height of the state to query
    -p, --proof PROOF         whether proof is required
```

__Example__

Query the channel end of channel `channel-1` on `ibc-1`:

```shell
$ hermes query channel end ibc-1 channel-1 | jq
```

```json
{
  "status": "success",
  "result": {
    "connection_hops": [
      "connection-1"
    ],
    "ordering": "Unordered",
    "remote": {
      "channel_id": "channel-0",
      "port_id": "transfer"
    },
    "state": "Open",
    "version": "ics20-1"
  }
}
```


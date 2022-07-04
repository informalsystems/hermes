# Transfer Queries

Use the `query transfer` command to query information about transfer(s).

```shell
USAGE:
    hermes query transfer <SUBCOMMAND>

DESCRIPTION:
    Query information about token transfers

SUBCOMMANDS:
    denom-trace    Query the denomination trace info from a trace hash
```

## Table of Contents

<!-- toc -->

## Denomination Trace

Use the `query transfer denom-trace` command to obtain the path and base denomination of a given trace hash.

```shell
USAGE:
    hermes query transfer denom-trace --chain <CHAIN_ID> --hash <HASH>

DESCRIPTION:
    Query the denomination trace info from a trace hash

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain
        --hash <HASH>         Trace hash to query
```

__Example__

Query chain `ibc-1` for the path and base denomination of the trace hash `27A6394C3F9FF9C9DCF5DFFADF9BB5FE9A37C7E92B006199894CF1824DF9AC7C`:

```shell
hermes query transfer denom-trace --chain ibc-1 --hash 27A6394C3F9FF9C9DCF5DFFADF9BB5FE9A37C7E92B006199894CF1824DF9AC7C
```

```shell
Success: base_denom: samoleans
 path: transfer/channel-0
```

Or with a JSON output:

```shell
hermes query transfer denom-trace --chain ibc-1 --hash 27A6394C3F9FF9C9DCF5DFFADF9BB5FE9A37C7E92B006199894CF1824DF9AC7C
```

```json
{
    "result":{
        "base_denom":"samoleans",
        "path":"transfer/channel-0"
    },
    "status":"success"
}
```
# Transfer Queries

Use the `query transfer` command to query information about transfer(s).

```shell
{{#template ../../../templates/help_templates/query/transfer.md}}
```

## Table of Contents

<!-- toc -->

## Denomination Trace

Use the `query transfer denom-trace` command to obtain the path and base denomination of a given trace hash.

```shell
{{#template ../../../templates/help_templates/query/transfer/denom-trace.md}}
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
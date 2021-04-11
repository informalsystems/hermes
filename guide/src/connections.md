# Connection

## Table of Contents
<!-- toc -->

## Establish Connection
Use the `create connection` command to create a new connection.

```shell
USAGE:
    hermes create connection <OPTIONS>

DESCRIPTION:
    Create a new connection between two chains

POSITIONAL ARGUMENTS:
    chain_a_id                identifier of the side `a` chain for the new connection
    chain_b_id                identifier of the side `b` chain for the new connection

FLAGS:
    --client-a CLIENT-A       identifier of client hosted on chain `a`; default: None (creates a new client)
    --client-b CLIENT-B       identifier of client hosted on chain `b`; default: None (creates a new client)

```

__Example__


```shell
hermes create connection ibc-0 ibc-1 | jq
```

```json

```

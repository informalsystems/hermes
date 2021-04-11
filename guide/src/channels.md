# Channel

## Table of Contents
<!-- toc -->

## Establish Channel
Use the `create channel` command to establish a new channel.

```shell
USAGE:
    hermes create channel <OPTIONS>

DESCRIPTION:
    Create a new channel between two chains

POSITIONAL ARGUMENTS:
    chain_a_id                identifier of the side `a` chain for the new channel
    chain_b_id                identifier of the side `b` chain for the new channel (optional)

FLAGS:
    -c, --connection-a CONNECTION-A
    --port-a PORT-A           identifier of the side `a` port for the new channel
    --port-b PORT-B           identifier of the side `b` port for the new channel
    -o, --order ORDER         the order for parametrizing the new channel
    -v, --version VERSION     the version for parametrizing the new channel

```

__Example__


```shell
hermes create channel ibc-0 ibc-1 | jq
```

```json

```

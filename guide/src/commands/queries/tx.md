# Tx Queries

Use the `query tx` command to query information about transaction(s).


```shell
USAGE:
    hermes query tx <SUBCOMMAND>

DESCRIPTION:
    Query information about transactions

SUBCOMMANDS:
    events     Query the events emitted by transaction
```

## Table of Contents

<!-- toc -->


## Transaction Events

Use the `query tx events` command to obtain a list of events that a chain generated as a consequence of
delivering a transaction.

```shell
USAGE:
    hermes query tx events <OPTIONS>

DESCRIPTION:
    Query the events emitted by transaction

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain to query
    hash                      transaction hash to query
```

__Example__

Query chain `ibc-0` for the events emitted due to transaction with hash
`6EDBBCBCB779F9FC9D6884ACDC4350E69720C4B362E4ACE6C576DE792F837490`:

```shell
hermes query tx events ibc-0 6EDBBCBCB779F9FC9D6884ACDC4350E69720C4B362E4ACE6C576DE792F837490
```

```json
Success: [
    SendPacket(
        SendPacket {
            height: Height {
                revision: 4,
                height: 6628239,
            },
            packet: PortId("transfer") ChannelId("channel-139") Sequence(2),
        },
    ),
]
```
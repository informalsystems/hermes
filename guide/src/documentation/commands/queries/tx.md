# Tx Queries

Use the `query tx` command to query information about transaction(s).


```shell
{{#template ../../../templates/help_templates/query/tx.md}}
```

## Table of Contents

<!-- toc -->


## Transaction Events

Use the `query tx events` command to obtain a list of events that a chain generated as a consequence of
delivering a transaction.

```shell
{{#template ../../../templates/help_templates/query/tx/events.md}}
```

__Example__

Query chain `ibc-0` for the events emitted due to transaction with hash
`6EDBBCBCB779F9FC9D6884ACDC4350E69720C4B362E4ACE6C576DE792F837490`:

```shell
hermes query tx events --chain ibc-0 --hash 6EDBBCBCB779F9FC9D6884ACDC4350E69720C4B362E4ACE6C576DE792F837490
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

# Table of Contents

<!-- toc -->

# Query Channels

Use the `query channels` command to query the identifiers of all channels on a given chain.

```shell
{{#include ../../../templates/help_templates/query/channels.md}}
```

__Example__

Query all channels on `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/query/channels_1.md CHAIN_ID=ibc-1}}
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
{{#include ../../../templates/help_templates/query/channel.md}}
```

## Query the channel end data

Use the `query channel end` command to query the channel end:

```shell
{{#include ../../../templates/help_templates/query/channel/end.md}}
```

__Example__

Query the channel end of channel `channel-1` on port `transfer` on `ibc-1`:

```shell
{{#template ../../../templates/commands/hermes/query/channel/end_1.md CHAIN_ID=ibc-1 PORT_ID=transfer CHANNEL_ID=channel-1}}
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
{{#include ../../../templates/help_templates/query/channel/ends.md}}
```

__Example__

Query the channel end of channel `channel-1` on port `transfer` on `ibc-0`:

```shell
{{#template ../../../templates/commands/hermes/query/channel/ends_1.md CHAIN_ID=ibc-0 PORT_ID=transfer CHANNEL_ID=channel-1}}
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

Passing the `--verbose` flag will additionally print all the details of the
channel, connection, and client on both ends.

## Query the channel client state

Use the `query channel client` command to obtain the channel's client state:

```shell
{{#include ../../../templates/help_templates/query/channel/client.md}}
```

If the command is successful a message with the following format will be displayed:
```
Success: Some(
    IdentifiedAnyClientState {
        client_id: ClientId(
            "07-tendermint-0",
        ),
        client_state: Tendermint(
            ClientState {
                chain_id: ChainId {
                    id: "network2",
                    version: 0,
                },
                trust_threshold: TrustThreshold {
                    numerator: 1,
                    denominator: 3,
                },
                trusting_period: 1209600s,
                unbonding_period: 1814400s,
                max_clock_drift: 40s,
                latest_height: Height {
                    revision: 0,
                    height: 2775,
                },
                proof_specs: ProofSpecs(
                    [
                        ProofSpec(
                            ProofSpec {
                                leaf_spec: Some(
                                    LeafOp {
                                        hash: Sha256,
                                        prehash_key: NoHash,
                                        prehash_value: Sha256,
                                        length: VarProto,
                                        prefix: [
                                            0,
                                        ],
                                    },
                                ),
                                inner_spec: Some(
                                    InnerSpec {
                                        child_order: [
                                            0,
                                            1,
                                        ],
                                        child_size: 33,
                                        min_prefix_length: 4,
                                        max_prefix_length: 12,
                                        empty_child: [],
                                        hash: Sha256,
                                    },
                                ),
                                max_depth: 0,
                                min_depth: 0,
                            },
                        ),
                        ProofSpec(
                            ProofSpec {
                                leaf_spec: Some(
                                    LeafOp {
                                        hash: Sha256,
                                        prehash_key: NoHash,
                                        prehash_value: Sha256,
                                        length: VarProto,
                                        prefix: [
                                            0,
                                        ],
                                    },
                                ),
                                inner_spec: Some(
                                    InnerSpec {
                                        child_order: [
                                            0,
                                            1,
                                        ],
                                        child_size: 32,
                                        min_prefix_length: 1,
                                        max_prefix_length: 1,
                                        empty_child: [],
                                        hash: Sha256,
                                    },
                                ),
                                max_depth: 0,
                                min_depth: 0,
                            },
                        ),
                    ],
                ),
                upgrade_path: [
                    "upgrade",
                    "upgradedIBCState",
                ],
                allow_update: AllowUpdate {
                    after_expiry: true,
                    after_misbehaviour: true,
                },
                frozen_height: None,
            },
        ),
    },
)
```

**JSON output:**

```shell
{{#template ../../../templates/commands/hermes/query/channel/client_1.md CHAIN_ID=<CHAIN_ID> PORT_ID=<PORT_ID> CHANNEL_ID=<CHANNEL_ID> GLOBALOPTIONS=  --json}}
```

If the command is successful a message with the following format will be displayed:

```json
{
    "result":
    {
        "client_id":"07-tendermint-0",
        "client_state":
        {
            "allow_update":
            {
                "after_expiry":true,
                "after_misbehaviour":true
            },
            "chain_id":"network2",
            "frozen_height":null,
            "latest_height":
            {
                "revision_height":2775,
                "revision_number":0
            },
            "max_clock_drift":
            {
                "nanos":0,
                "secs":40
            },
            "proof_specs":
            [
                {
                    "inner_spec":
                    {
                        "child_order":[0,1],
                        "child_size":33,
                        "empty_child":"",
                        "hash":1,
                        "max_prefix_length":12,
                        "min_prefix_length":4
                    },
                    "leaf_spec":
                    {
                        "hash":1,
                        "length":1,
                        "prefix":"AA==",
                        "prehash_key":0,
                        "prehash_value":1
                    },
                    "max_depth":0,
                    "min_depth":0
                },
                {
                    "inner_spec":
                    {
                        "child_order":[0,1],
                        "child_size":32,
                        "empty_child":"",
                        "hash":1,
                        "max_prefix_length":1,
                        "min_prefix_length":1
                    },
                    "leaf_spec":
                    {
                        "hash":1,
                        "length":1,
                        "prefix":"AA==",
                        "prehash_key":0,
                        "prehash_value":1
                    },
                    "max_depth":0,
                    "min_depth":0
                }
            ],
            "trust_threshold":
            {
                "denominator":3,
                "numerator":1
            },
            "trusting_period":
            {
                "nanos":0,
                "secs":1209600
            },
            "type":"Tendermint",
            "unbonding_period":
            {
                "nanos":0,
                "secs":1814400
            },
            "upgrade_path":["upgrade","upgradedIBCState"]
        },
        "type":"IdentifiedAnyClientState"
    },
    "status":"success"
}
```

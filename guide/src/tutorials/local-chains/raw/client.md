# 1. Configuring clients

### 1.1. `create client`

First you will need to create a client for each chain:

This command submits a transaction to a destination chain (`ibc-0`) with a request to create a client for a source chain (`ibc-1`):

```shell
hermes create client --host-chain ibc-0 --reference-chain ibc-1
```

if the command is successful a message similar to the one below will be displayed `status:success`:

```json
{
    Success: CreateClient(
        CreateClient(
            Attributes {
                height: Height { revision: 0, height: 43 },
                client_id: ClientId(
                    "07-tendermint-0",
                ),
                client_type: Tendermint,
                consensus_height: Height { revision: 1, height: 32 },
            },
        ),
    )
}
```

> Please note the `client_id` value returned. You will need that for other commands.

You can also execute a __query__ to view the client state on destination chain `ibc-0` by specifying the `client_id` value `07-tendermint-0`:

```shell
hermes query client state --chain ibc-0 --client 07-tendermint-0
```

which show a message similar to the one below:

```json
Success: ClientState {
    chain_id: ChainId {
        id: "ibc-1",
        version: 1,
    },
    trust_level: TrustThresholdFraction {
        numerator: 1,
        denominator: 3,
    },
    trusting_period: 1209600s,
    unbonding_period: 1814400s,
    max_clock_drift: 3s,
    frozen_height: Height {
        revision: 0,
        height: 0,
    },
    latest_height: Height {
        revision: 1,
        height: 38,
    },
    upgrade_path: [
        "upgrade",
        "upgradedIBCState",
    ],
    allow_update_after_expiry: true,
    allow_update_after_misbehaviour: true,
}
```

Now let's do the same for `ibc-1` as the destination chain:

```shell
hermes create client --host-chain ibc-1 --reference-chain ibc-0
```

Take note of the `client_id` allocated for this client. In the examples we assume is `07-tendermint-1` (this client identity is obtained by creating two clients on ibc-1 for ibc-0).

As before, if the command is successful a message with `status:success` is displayed:

```json
Success: CreateClient(
    CreateClient(
        Attributes {
            height: Height {
                revision: 1,
                height: 135,
            },
            client_id: ClientId(
                "07-tendermint-1",
            ),
            client_type: Tendermint,
            consensus_height: Height {
                revision: 0,
                height: 145,
            },
        },
    ),
)
```

### 1.2 `update client`

Client states can be updated by sending an `update-client` transaction:

```shell
hermes update client --host-chain ibc-0 --client 07-tendermint-0
```

```shell
hermes update client --host-chain ibc-1 --client 07-tendermint-1
```

## Next Steps

In the next section, we'll establish the [Connection Handshake](./connection.md)

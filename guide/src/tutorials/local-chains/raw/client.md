# 1. Configuring clients

### 1.1. `create client`

First you will need to create a client for each chain:

This command submits a transaction to a destination chain (`ibc-0`) with a request to create a client for a source chain (`ibc-1`):

```shell
hermes tx raw create-client ibc-0 ibc-1 | jq
```

if the command is successful a message similar to the one below will be displayed `status:success`:

```json
{
    "status": "success",
    "result": [
        {
            "CreateClient": {
                "client_id": "07-tendermint-0",
                "client_type": "Tendermint",
                "consensus_height": {
                    "revision_height": 998,
                    "revision_number": 1
                  },
                  "height": {
                    "revision_height": 1009,
                    "revision_number": 0
                  }
            }
        }
    ]
}
```

> Please note the `client_id` value returned. You will need that for other commands.

You can also execute a __query__ to view the client state on destination chain `ibc-0` by specifying the `client_id` value `07-tendermint-0`:

```shell
hermes query client state ibc-0 07-tendermint-0  | jq
```

which show a message similar to the one below:

```json
{
  "status": "success",
  "result": {
    "type": "Tendermint",
    "allow_update_after_expiry": false,
    "allow_update_after_misbehaviour": false,
    "chain_id": "ibc-1",
    "frozen_height": {
      "revision_height": 0,
      "revision_number": 0
    },
    "latest_height": {
      "revision_height": 981,
      "revision_number": 1
    },
    "max_clock_drift": {
      "nanos": 0,
      "secs": 3
    },
    "trust_level": {
      "denominator": "3",
      "numerator": "1"
    },
    "trusting_period": {
      "nanos": 0,
      "secs": 1209600
    },
    "unbonding_period": {
      "nanos": 0,
      "secs": 1814400
    },
    "upgrade_path": [
      "upgrade",
      "upgradedIBCState"
    ]
  }
}
```

Now let's do the same for `ibc-1` as the destination chain:

```shell
hermes tx raw create-client ibc-1 ibc-0 | jq
```

Take note of the `client_id` allocated for this client. In the examples we assume is `07-tendermint-1` (this client identity is obtained by creating two clients on ibc-1 for ibc-0).

As before, if the command is successful a message with `status:success` is displayed:

```json
{
    "status": "success",
    "result": {
        "CreateClient": {
            "client_id": "07-tendermint-1",
            "client_type": "Tendermint",
            "consensus_height": {
                "revision_height": 1162,
                "revision_number": 0
            },
            "height": {
                "revision_height": 1154,
                "revision_number": 1
              }
        }
    }
}
```

### 1.2 `update-client`

Client states can be updated by sending an `update-client` transaction:

```shell
hermes tx raw update-client ibc-0 07-tendermint-0
```

```shell
hermes tx raw update-client ibc-0 07-tendermint-1
```

## Next Steps

In the next section, we'll establish the [Connection Handshake](./connection.md)

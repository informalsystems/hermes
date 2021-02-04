# Client
The `tx raw` commands can be used to create and update the on-chain IBC clients.

## Create Client
Use the `create-client` command to create a new client.

```shell
USAGE:
    hermes tx raw create-client <OPTIONS>

DESCRIPTION:
    tx raw create-client

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain

```

__Example__

Create a new client of `ibc-1` on `ibc-0`:

```shell
hermes tx raw create-client ibc-0 ibc-1 | jq
```

```json
{
  "status": "success",
  "result": {
    "CreateClient": {
      "client_id": "07-tendermint-0",
      "client_type": "Tendermint",
      "consensus_height": {
        "revision_height": 18,
        "revision_number": 1
      },
      "height": "1"
    }
  }
}
```

A new client is created with identifier `07-tendermint-0`

## Update Client
Use the `update-client` command to update an existing client with a new consensus state.

```shell
USAGE:
    hermes tx raw update-client <OPTIONS>

DESCRIPTION:
    tx raw update-client

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    dst_client_id             identifier of the client to be updated on destination chain
```

__Example__

Update the client on `ibc-0` with latest header of `ibc-1`

```shell
hermes tx raw update-client ibc-0 ibc-1 07-tendermint-0  | jq
```

```json
{
  "status": "success",
  "result": {
    "UpdateClient": {
      "client_id": "07-tendermint-0",
      "client_type": "Tendermint",
      "consensus_height": {
        "revision_height": 273,
        "revision_number": 1
      },
      "height": "1"
    }
  }
}
```

The client with identifier `07-tendermint-0` has been updated with the consensus state at height `1-273`.

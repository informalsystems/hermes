# Connection Handshake

The `tx raw` commands can be used to establish a connection between two clients.

## Connection Init

Use the `conn-init` command to initialize a new connection on a chain.

```shell
USAGE:
    hermes tx raw conn-init <OPTIONS>

DESCRIPTION:
    Initialize a connection attempt on chain A

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    dst_client_id             identifier of the destination client
    src_client_id             identifier of the source client
```

__Example__

Given that two clients were previously created with identifier `07-tendermint-0` on chain `ibc-0` and
identifier `07-tendermint-1` on chain `ibc-1`, we can initialize a connection between the two clients.

First, let's initialize the connection on `ibc-0`:

```shell
$ hermes -c config.toml tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-1
```

```json
{
  "status": "success",
  "result": [
    {
      "OpenInitConnection": {
        "client_id": "07-tendermint-0",
        "connection_id": "connection-0",
        "counterparty_client_id": "07-tendermint-1",
        "counterparty_connection_id": null,
        "height": "1"
      }
    }
  ]
}
```

A new connection has been initialized on `ibc-0` with identifier `connection-0`.
Note that the `counterparty_connection_id` field is currently empty.


## Connection Try

Use the `conn-try` command to establish a counterparty to the connection on the other chain.

```shell
USAGE:
    hermes tx raw conn-try <OPTIONS>

DESCRIPTION:
    Relay notice of a connection attempt on chain A to chain B

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    dst_client_id             identifier of the destination client
    src_client_id             identifier of the source client

FLAGS:
    -s, --src-conn-id ID      identifier of the source connection (required)
```

__Example__

Let's now create the counterparty to `connection-0` on chain `ibc-1`:

```shell
$ hermes -c config.toml tx raw conn-try ibc-1 ibc-0 07-tendermint-1 07-tendermint-0 -s connection-0 | jq
```

```json
{
  "status": "success",
  "result": [
    {
      "OpenTryConnection": {
        "client_id": "07-tendermint-1",
        "connection_id": "connection-1",
        "counterparty_client_id": "07-tendermint-0",
        "counterparty_connection_id": "connection-0",
        "height": "1"
      }
    }
  ]
}
```

A new connection has been created on `ibc-1` with identifier `connection-1`.
Note that the field `counterparty_connection_id` points to the connection on `ibc-0`.


## Connection Ack

Use the `conn-ack` command to acknowledge the connection on the initial chain.

```shell
USAGE:
    hermes tx raw conn-ack <OPTIONS>

DESCRIPTION:
    Relay acceptance of a connection attempt from chain B back to chain A

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    dst_client_id             identifier of the destination client
    src_client_id             identifier of the source client

FLAGS:
    -d, --dst-conn-id ID      identifier of the destination connection (required)
    -s, --src-conn-id ID      identifier of the source connection (required)
```

__Example__

```shell
$ hermes -c config.toml tx raw conn-ack ibc-0 ibc-1 07-tendermint-0 07-tendermint-1 -d connection-0 -s connection-1 | jq
```

```json
{
  "status": "success",
  "result": [
    {
      "OpenAckConnection": {
        "client_id": "07-tendermint-0",
        "connection_id": "connection-0",
        "counterparty_client_id": "07-tendermint-1",
        "counterparty_connection_id": "connection-1",
        "height": "1"
      }
    }
  ]
}
```

Note that the field `counterparty_connection_id` now points to the connection on `ibc-1`.


## Connection Confirm

Use the `conn-confirm` command to confirm that the connection has been acknowledged,
and finish the handshake.

```shell
USAGE:
    hermes tx raw conn-confirm <OPTIONS>

DESCRIPTION:
    Confirm opening of a connection on chain A to chain B, after which the connection is open on both chains

POSITIONAL ARGUMENTS:
    dst_chain_id              identifier of the destination chain
    src_chain_id              identifier of the source chain
    dst_client_id             identifier of the destination client
    src_client_id             identifier of the source client

FLAGS:
    -d, --dst-conn-id ID      identifier of the destination connection (required)
    -s, --src-conn-id ID      identifier of the source connection (required)
```

__Example__

```shell
$ hermes -c config.toml tx raw conn-confirm ibc-1 ibc-0 07-tendermint-1 07-tendermint-0 -d connection-1 -s connection-0 | jq
```

```json
{
  "status": "success",
  "result": [
    {
      "OpenConfirmConnection": {
        "client_id": "07-tendermint-1",
        "connection_id": "connection-1",
        "counterparty_client_id": "07-tendermint-0",
        "counterparty_connection_id": "connection-0",
        "height": "1"
      }
    }
  ]
}
```

We have now successfully established a connection between the two chains.


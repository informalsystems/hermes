# REST API

*Since version 0.7.0.*

Hermes features a built-in HTTP server which exposes information
about the relayer configuration and state via a REST API.

## Table of Contents

<!-- toc -->

## Configuration

The REST API is not active by default, and must be enabled in the relayer configuration:

```toml
[rest]
enabled = true
host    = '127.0.0.1'
port    = 3000
```

Please see the [relevant section in the *Configuration* page](./config.md#rest) for details about the configuration options.

## Endpoints

### GET `/version`

This endpoint returns the version of the Hermes (under the `ibc-relayer` key) as well
as the version of the REST server itself (under the `ibc-relayer-rest` key).

**Example**

```
❯ curl -s -X GET 'http://127.0.0.1:3000/version' | jq
```

```json
[
  {
    "name": "ibc-relayer",
    "version": "0.13.0-rc.0"
  },
  {
    "name": "ibc-relayer-rest",
    "version": "0.1.0"
  }
]
```

### GET `/chains`

This endpoint return the identifiers of the chains that Hermes is connected to.
Those identifiers can be used with the `/chain/:id` endpoint to gather more
information about each chain's configuration. See the next section for more details.

**Example**

```
❯ curl -s -X GET 'http://127.0.0.1:3000/chains' | jq
```

```json
{
  "status": "success",
  "result": [
    "ibc-0",
    "ibc-1"
  ]
}
```

### GET `/chain/:id`

This endpoint returns the configuration of the chain with the given identifier,
where `:id` stands for the identififer.

**Example**

```
❯ curl -s -X GET 'http://127.0.0.1:3000/chain/ibc-0' | jq
```

```json
{
  "status": "success",
  "result": {
    "id": "ibc-0",
    "rpc_addr": "http://127.0.0.1:26657/",
    "websocket_addr": "ws://127.0.0.1:26657/websocket",
    "grpc_addr": "http://127.0.0.1:9090/",
    "rpc_timeout": "10s",
    "account_prefix": "cosmos",
    "key_name": "testkey",
    "store_prefix": "ibc",
    "max_gas": 900000000,
    "gas_adjustment": null,
    "max_msg_num": 60,
    "max_tx_size": 2097152,
    "clock_drift": "5s",
    "trusting_period": "14days",
    "trust_threshold": {
      "numerator": "1",
      "denominator": "3"
    },
    "gas_price": {
      "price": 0.001,
      "denom": "stake"
    },
    "packet_filter": {
      "policy": "allowall"
    }
  }
}
```

### GET `/state`

This endpoint returns the current state of the relayer,
namely which chains it is connected to, as well as a description
of all the workers which are currently active.

```
❯ curl -s -X GET 'http://127.0.0.1:3000/state' | jq
```

```json
{
  "status": "success",
  "result": {
    "chains": [
      "ibc-0",
      "ibc-1"
    ],
    "workers": {
      "Client": [
        {
          "id": 3,
          "object": {
            "type": "Client",
            "dst_chain_id": "ibc-1",
            "dst_client_id": "07-tendermint-0",
            "src_chain_id": "ibc-0"
          }
        },
        {
          "id": 4,
          "object": {
            "type": "Client",
            "dst_chain_id": "ibc-1",
            "dst_client_id": "07-tendermint-1",
            "src_chain_id": "ibc-0"
          }
        },
        {
          "id": 1,
          "object": {
            "type": "Client",
            "dst_chain_id": "ibc-0",
            "dst_client_id": "07-tendermint-0",
            "src_chain_id": "ibc-1"
          }
        },
        {
          "id": 2,
          "object": {
            "type": "Client",
            "dst_chain_id": "ibc-0",
            "dst_client_id": "07-tendermint-1",
            "src_chain_id": "ibc-1"
          }
        }
      ]
    }
  }
}
```

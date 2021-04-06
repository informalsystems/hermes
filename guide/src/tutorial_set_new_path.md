# Create a new path

Perform client creation, connection and channel handshake to establish a new path between the `transfer` ports on `ibc-0` and `ibc-1` chains.

OUT of DATE 

```shell script
hermes channel handshake ibc-0 ibc-1 transfer transfer
```

```json
{
  "status": "success",
  "result": {
    "a_side": {
      "chain": "ibc-1",
      "channel_id": "channel-3",
      "client_id": "07-tendermint-3",
      "connection_id": "connection-2",
      "port_id": "transfer"},
    "b_side": {
      "chain": "ibc-0",
      "channel_id": "channel-1",
      "client_id": "07-tendermint-1",
      "connection_id": "connection-3",
      "port_id": "transfer"
    },
    "ordering":"Unordered"
  }
}
```

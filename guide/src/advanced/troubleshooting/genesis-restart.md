# Updating a client after a Genesis restart without IBC upgrade proposal

If a chain went through a genesis restart without an IBC upgrade proposal updating the client can result in an error due to blocks at lower heights not being available.

For example if we have two chains `ibc-0` and `ibc-1`, a client `07-tendermint-0` hosted on chain `ibc-1` referencing `ibc-0` and an Archive Node with its RPC address `http://127.0.0.1:28000`. After `ibc-0` goes through a genesis restart without an IBC upgrade proposal, trying to update client `07-tendermint-0` will result in an error:

```
ERROR failed during a client operation: error raised while updating client: failed
building header with error: Light client error for RPC address network1-1:
Internal error: height 26 is not available, lowest height is 1101 (code: -32603):
```

In this case, to update the client at a height higher than `1101` for example `1102`, the following command can be used.

```shell
{{#template ../../templates/commands/hermes/update/client_1.md HOST_CHAIN_ID=ibc-1 CLIENT_ID=07-tendermint-0 OPTIONS= --height 1102 --archive-address http://127.0.0.1:28000 --restart-height 1101}}
```

Once this command is successful, updating the client should then work as usual.
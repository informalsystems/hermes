# IBC Test

The `simapp` directory contains complete data for running an IBC enabled
blockchain using the `simd` app from the `Cosmos-SDK`.

It also comes with an account key for sending txs - the password is `asdfghjkl;'`

Run using Docker:
```
docker run --rm -p 1317:1317 -p 26657:26657 informaldev/simd
```

Or install `simd` from the cosmos-sdk repo and run it with this genesis data:

```
git clone https://github.com/comsos/cosmos-sdk
cd cosmos-sdk
make build-simd
build/simd --home simapp start
```

This will start an IBC enabled blockchain with some initial IBC state that you
can then query. For instance:

Tendermint RPC:
```
curl 'localhost:26657/abci_query?path="store/ibc/key"&data="connections/connectionidone"'
curl 'localhost:26657/abci_query?path="store/ibc/key"&data="clients/ethbridge/clientState"&prove=true'
curl 'localhost:26657/abci_query?path="store/ibc/key"&data="channelEnds/ports/firstport/channels/firstchannel"'
```

will return the relevent proto encoded data.


Cosmos SDK RPC:
```
curl 'localhost:1317/ibc/connections'
curl 'localhost:1317/ibc/clients'
```

will return the relevant JSON-encoded data.

:D

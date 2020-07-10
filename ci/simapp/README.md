# IBC Test

The `simapp` directory contains complete data for running an IBC enabled
blockchain using the `simd` app from the `Cosmos-SDK`.

It also comes with an account key for sending txs - the password is `asdfghjkl;'`

Run using Docker:
```
docker run --rm -p 26657:26657 informaldev/simd
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

```
curl 'localhost:26657/abci_query?path="store/ibc/key"&data="connections/connectionidone"'
curl 'localhost:26657/abci_query?path="store/ibc/key"&data="clients/ethbridge"'
curl 'localhost:26657/abci_query?path="store/ibc/key"&data="channels/firstchannel"'
```

will return the relevent proto encoded connection data.


:D

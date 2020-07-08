# IBC Test

The `.simapp` directory contains complete data for running an IBC enabled
blockchain using the `simd` app from the `Cosmos-SDK`.

It also comes with an account key for sending txs - the password is `asdfghjkl;'`

Install `simd` from the cosmos-sdk repo:

```
go install ./simapp/simd/
```

Run it with this genesis data:

```
simd --home simapp start
```

This will start an IBC enabled blockchain with some initial IBC state that you
can then query. For instance:

```
curl 'localhost:26657/abci_query?path="store/ibc/key"&data="connections/connectionidone"'
```

will return the relevent proto encoded connection data.


:D

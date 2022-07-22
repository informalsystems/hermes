# 2. Connection Handshake

## 2.1 `conn-init`

Initialize a new connection on `ibc-0`:
```shell
hermes conn-init --b-chain ibc-0 --a-chain ibc-1 --b-client 07-tendermint-0 --a-client 07-tendermint-1
```

Take note of the ID allocated by the chain, e.g. `connection-0` on `ibc-0` in order to use it in the `conn-try` command below.

## 2.2 `conn-try`

Send a connection try to `ibc-1`:
```shell
hermes tx conn-try --b-chain ibc-1 --a-chain ibc-0 --b-client 07-tendermint-1 --a-client 07-tendermint-0 --a-connection connection-0
```

Take note of the ID allocated by the chain, e.g. `connection-1` on `ibc-1`. Use in the `conn-ack` CLI

## 2.3 `conn-ack`

Send a connection open acknowledgment to `ibc-0`:
```shell
hermes tx conn-ack --b-chain ibc-0 --a-chain ibc-1 --b-client 07-tendermint-0 --a-client 07-tendermint-1 --b-connection connection-0 --a-connection connection-1
```

## 2.4 `conn-confirm`

Send the open confirmation to `ibc-1`:
```shell
hermes tx conn-confirm --b-chain ibc-1 --a-chain ibc-0 --b-client 07-tendermint-1 --a-client 07-tendermint-0 --b-connection connection-1 --a-connection connection-0
```

## 2.5 `query connection`

To verify that the two ends are in `Open` state:

```shell
hermes query connection end --chain ibc-0 --connection connection-0
```

```shell
hermes query connection end --chain ibc-1 --connection connection-1
```


## Next Steps

In the next section, we'll [establish a new channel](./channel.md)

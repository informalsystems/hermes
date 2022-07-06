# 2. Connection Handshake

## 2.1 `conn-init`

Initialize a new connection on `ibc-0`:
```shell
hermes tx raw conn-init --dst-chain ibc-0 --src-chain ibc-1 --dst-client 07-tendermint-0 --src-client 07-tendermint-1
```

Take note of the ID allocated by the chain, e.g. `connection-0` on `ibc-0` in order to use it in the `conn-try` command below.

## 2.2 `conn-try`

Send a connection try to `ibc-1`:
```shell
hermes tx raw conn-try --dst-chain ibc-1 --src-chain ibc-0 --dst-client 07-tendermint-1 --src-client 07-tendermint-0 --src-conn connection-0
```

Take note of the ID allocated by the chain, e.g. `connection-1` on `ibc-1`. Use in the `conn-ack` CLI

## 2.3 `conn-ack`

Send a connection open acknowledgment to `ibc-0`:
```shell
hermes tx raw conn-ack --dst-chain ibc-0 --src-chain ibc-1 --dst-client 07-tendermint-0 --src-client 07-tendermint-1 --dst-conn connection-0 --src-conn connection-1
```

## 2.4 `conn-confirm`

Send the open confirmation to `ibc-1`:
```shell
hermes tx raw conn-confirm --dst-chain ibc-1 --src-chain ibc-0 --dst-client 07-tendermint-1 --src-client 07-tendermint-0 --dst-conn connection-1 --src-conn connection-0
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

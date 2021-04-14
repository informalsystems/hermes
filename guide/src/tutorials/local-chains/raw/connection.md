# 2. Connection Handshake

## 2.1 `conn-init`

Initialize a new connection on `ibc-0`:
```shell
hermes tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-1
```

Take note of the ID allocated by the chain, e.g. `connection-0` on `ibc-0` in order to use it in the `conn-try` command below.

## 2.2 `conn-try`

Send a connection try to `ibc-1`:
```shell
hermes tx raw conn-try ibc-1 ibc-0 07-tendermint-1 07-tendermint-0 -s connection-0
```

Take note of the ID allocated by the chain, e.g. `connection-1` on `ibc-1`. Use in the `conn-ack` CLI

## 2.3 `conn-ack`

Send a connection open acknowledgment to `ibc-0`:
```shell
hermes tx raw conn-ack ibc-0 ibc-1 07-tendermint-0 07-tendermint-1 -d connection-0 -s connection-1
```

## 2.4 `conn-confirm`

Send the open confirmation to `ibc-1`:
```shell
hermes tx raw conn-confirm ibc-1 ibc-0 07-tendermint-1 07-tendermint-0 -d connection-1 -s connection-0
```

## 2.5 `query connection`

To verify that the two ends are in `Open` state:

```shell
hermes query connection end ibc-0 connection-0
```

```shell
hermes query connection end ibc-1 connection-1
```


## Next Steps

In the next section, we'll [establish a new channel](./channel.md)

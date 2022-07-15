# 3. Channel Handshake

## 3.1 `chan-open-init`

Initialize a new unordered channel on `ibc-0`:
```shell
hermes tx chan-open-init --b-chain ibc-0 --a-chain ibc-1 --b-connection connection-0 --b-port transfer --a-port transfer --order UNORDERED
```

## 3.2 `chan-open-try`

Send a channel open try to `ibc-1`:
```shell
hermes tx chan-open-try --b-chain ibc-1 --a-chain ibc-0 --b-connection connection-1 --b-port transfer --a-port transfer --a-channel channel-0
```

Take note of the ID allocated by the chain, e.g. `channel-1` on `ibc-1`. Use in the `chan-open-ack` CLI

## 3.3 `chan-open-ack`

Send a channel open acknowledgment to `ibc-0`:
```shell
hermes tx chan-open-ack --b-chain ibc-0 --a-chain ibc-1 --b-connection connection-0 --b-port transfer --a-port transfer --b-channel channel-0 --a-channel channel-1
```

## 3.4 `chan-open-confirm`

Send the open confirmation to `ibc-1`:
```shell
hermes tx chan-open-confirm --b-chain ibc-1 --a-chain ibc-0 --b-connection connection-1 --b-port transfer --a-port transfer --b-channel channel-1 --a-channel channel-0
```

## 3.5 `query channel`
To verify that the two ends are in `Open` state:

```shell
hermes query channel end --chain ibc-0 --port transfer --channel channel-0
```

```shell
hermes query channel end --chain ibc-1 --port transfer --channel channel-1
```

## Next Steps

In the next section, we'll start to [relay packets](./packet.md)

# 3. Open the Channel

### 3.1 chan-open-init

```shell
hermes tx raw chan-open-init ibc-0 ibc-1 connection-0 transfer transfer defaultChannel defaultChannel
```

### 3.2 chan-open-try
__Note__: If this is the first channel to be created on `ibc-1`, prior to the `chan-open-try` command, you can send a `chan-open-init` to `ibc-1` and the chain will allocate `channel-0`. This will ensure that the next available ID, `channel-1`, will be allocated in `chan-open-try`.

```shell
hermes tx raw chan-open-init ibc-1 ibc-0 connection-0 transfer transfer defaultChannel defaultChannel
```

To send the `chan-open-try` message to `ibc-1`:

```shell
hermes tx raw chan-open-try ibc-1 ibc-0 connection-1 transfer transfer defaultChannel channel-0
```

Take note of the ID allocated by the chain, e.g. `channel-1` on `ibc-1`. Use in the `chan-open-ack` CLI

### 3.3 chan-open-ack

```shell
hermes tx raw chan-open-ack ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-1
```

### 3.4 chan-open-confirm

```shell
hermes tx raw chan-open-confirm ibc-1 ibc-0 connection-1 transfer transfer channel-1 channel-0
```

### 3.5 query channel
To verify that the two ends are in `Open` state:

```shell
hermes query channel end ibc-0 transfer channel-0
```

```shell
hermes query channel end ibc-1 transfer channel-1
```

## Next Steps

In the next section, we'll start to [Relay Packets](./relay_packet.md)
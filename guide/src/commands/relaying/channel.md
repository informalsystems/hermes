# Channel Message Relaying

This section describes the configuration and commands that can be used to start the relayer and relay both channel handshake and packets.

## The `start` Command

To relay packets and channel handshake messages use `all` as strategy in the `global` section of the configuration file:
```toml
[global]
strategy = 'all'
log_level = 'info'
```

Then start hermes using the start command:

```shell
hermes start
```

The relayer sends channel and packet transactions triggered by IBC events.

## Channel Open Handshake Relaying

After the relayer is started using the `start` command, it scans the chain state and will resume the handshake for any
channels that are not in open state. It then listens to IBC events emitted by any of
the configured chains.

Assuming the events are coming from a `source` chain, the relayer determines the `destination` chain and builds the open handshake messages based on these events. These are then sent to the `destination` chain.
In addition to the events described in [Packet Relaying](packets.md#packet-relaying), in the `all` strategy mode the following IBC events are handled:

- `chan_open_init`: the relayer builds a `MsgChannelOpenTry` message
- `chan_open_try`: the relayer builds a `MsgChannelOpenAck` message
- `chan_open_ack`: the relayer builds a `MsgChannelOpenConfirm` message
- `chan_open_confirm`: no message is sent out, channel opening is finished



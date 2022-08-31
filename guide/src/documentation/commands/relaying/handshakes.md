# Relaying of Handshake Messages

This section describes the configuration and commands that can be used to start the relayer and relay both handshake and packets
for connections and channels.

## The `start` Command

To relay packets and handshake messages configure the `mode` section of the configuration file like so:
```toml
[global]
log_level = 'info'

[mode]

[mode.clients]
enabled = true
# ...

[mode.connections]
enabled = true

[mode.channels]
enabled = true

[mode.packets]
enabled = true
# ...
```

Then start hermes using the start command:

```shell
hermes start
```

The relayer sends handshake and packet transactions triggered by IBC events.

## Completing Channel Handshakes

After the relayer is started using the `start` command, it scans the chain state and will resume the handshake for any
channels or connections that are not in open state. It then listens to IBC events emitted by any of
the configured chains.

Assuming the events are coming from a `source` chain, the relayer determines the `destination` chain and builds the handshake messages based on these events. These are then sent to the `destination` chain.

In addition to the events described in [Packet Relaying](packets.md#packet-relaying), the following IBC events may be handled:

- Channels (if `mode.channels.enabled=true`):
  - `chan_open_init`: the relayer builds a `MsgChannelOpenTry` message
  - `chan_open_try`: the relayer builds a `MsgChannelOpenAck` message
  - `chan_open_ack`: the relayer builds a `MsgChannelOpenConfirm` message
  - `chan_open_confirm`: no message is sent out, channel opening is finished

- Connections (if `mode.connections.enabled=true`):
  - `conn_open_init`: the relayer builds a `MsgConnOpenTry` message
  - `conn_open_try`: the relayer builds a `MsgConnOpenAck` message
  - `conn_open_ack`: the relayer builds a `MsgConnOpenConfirm` message
  - `conn_open_confirm`: no message is sent out, connection opening is finished


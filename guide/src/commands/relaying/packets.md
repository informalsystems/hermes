# Packet Relaying

This section describes the configuration and commands that can be used to start the relayer and relay packets over one or multiple paths.

## Table of Contents

<!-- toc -->

## The `start` Command

To relay packets only configure the `mode` section of the configuration file like so:
```toml
[global]
log_level = 'info'

[mode]

[mode.clients]
enabled = true
# ...

[mode.connections]
enabled = false

[mode.channels]
enabled = false

[mode.packets]
enabled = true
# ...
```

Then start hermes using the start command:

```shell
hermes start
```

The relayer sends packet transactions triggered by IBC packet events for all open channels between the configured chains.
This is also referred to packet streaming.

## Packet Streaming

After the relayer is started using the `start` command, it listens to IBC packet events emitted by any of
the configured chains. Assuming the events are coming from a `source` chain, the relayer builds packets
based on these events, packets that are then sent either to the `source` chain or the counterparty (`destination`) chain.

Current events and actions are:

- `send_packet`: the relayer builds a packet message with the `packet` obtained from the event and any required proofs obtained from the counterparty of the chain where the message is sent. The concrete packet is:
  - `MsgRecvPacket`, sent to `destination` chain if the channel is in open state on the `destination` chain, and a timeout has not occurred,
  - `MsgTimeout`, sent to the `source` chain if the channel is in open state on the `destination` chain, but a timeout has occurred.
  - `MsgTimeoutOnClose`, sent to the `source` chain if the channel is in closed state on the `destination` chain.
- `write_acknowledgement`: the relayer builds a `MsgAcknowledgement` packet that is sent to the `destination` chain.

In addition to these events, the relayer will also handle channel closing events:
- `chan_close_init`: the relayer builds a `MsgChannelCloseConfirm` and sends it to the `destination` chain

## Packet Delay

If the relay path is using a non-zero delay connection, then `hermes` will delay all packet transactions. The delay is relative to the submission time for the client update at the height required by the packet proof.
The delay is used to prevent light client attacks and ensures that misbehavior detection finalizes before the transaction is submitted.
For more information on the misbehavior detector see [the misbehaviour section](../misbehaviour/index.md#monitoring-misbehaviour-and-evidence-submission).


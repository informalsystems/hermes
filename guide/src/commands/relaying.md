# Packet Relaying

This section describes the commands that can be used to start the relayer and relay packets over one or multiple paths.

## Table of Contents

<!-- toc -->

## The `start` Command

The `start` command can be used to send packet transactions triggered by IBC packet events that occur for a given channel. This is also referred to packet streaming.
A new channel can be established or an existing one can be specified.

```shell
USAGE:
    hermes start <OPTIONS>

DESCRIPTION:
    start the relayer (currently this refers to the v0 relayer)

POSITIONAL ARGUMENTS:
    src_chain_id              identifier of the source chain
    dst_chain_id              identifier of the destination chain

FLAGS:
    -p, --src-port-id SRC-PORT-ID
    -c, --src-channel-id SRC-CHANNEL-ID
```

## Relay On A New Channel

Use the `start` command without flags to create new clients on `source` and `destination` chains, and new connection and new channel between the two chains.

> Reusing existing clients or connection is not possible with the current version. The port used by the channel is obtained from and must be specified in the configuration file.

__Example__

```shell
hermes start ibc-0 ibc-1
```

The relayer creates a new client on each chain and then established a new connection and a new channel using that connection. After that is enters a listen loop acting on packet events that occur on that channel.

## Relay On An Existing Channel

Use the `start` command and specify the source port and channel identifier of a channel that is already created and in open state on both chains.

__Example__

```shell
hermes start ibc-0 ibc-1 -p transfer -c channel-0
```

> Finishing uncompleted handshakes can only be achieved using the `tx raw` CLIs.

## Packet Streaming

After the relayer is started using the `start` command, it listens to IBC packet events for the channel. Assuming the events are coming from a `source` chain, the relayer builds packets based on these events, packets that are then sent either to the `source` chain or the counterparty (`destination`) chain.

Current events and actions are:

- `send_packet`: the relayer builds a packet message with the `packet` obtained from the event and any required proofs obtained from the counterparty of the chain where the message is sent. The concrete packet is:
  - `MsgRecvPacket`, sent to `destination` chain if the channel is in open state on the `destination` chain, and a timeout has not occurred,
  - `MsgTimeout`, sent to the `source` chain if the channel is in open state on the `destination` chain, but a timeout has occurred.
  - `MsgTimeoutOnClose`, sent to the `source` chain if the channel is in closed state on the `destination` chain.
- `write_acknowledgement`: the relayer builds a `MsgAcknowledgement` packet that is sent to the `destination` chain.

## Packet Delay

If the relay path is using a non-zero delay connection, then `hermes` will delay all packet transactions. The delay is
relative to the submission time for the client update at the height required by the packet proof.
The delay is used to prevent light client attacks and ensures that misbehavior detection finalizes before the transaction is submitted.
For more information on the misbehavior detector see [the misbehaviour section](./misbehaviour/index.md#monitoring-misbehaviour-and-evidence-submission).

## Relay On Multiple Paths

Unlike the `start` command which relay packets over a single path,
the `start-multi` command can be used to relay packets over all
existing channels between the configured chains.

> __WARNING:__ The functionality is currently experimental.

```shell
USAGE:
    hermes start-multi

DESCRIPTION:
    Start the relayer in multi-paths mode. Handles packet relaying across all open channels between all chains in the config.
```

__Note:__ When using the `start-multi` command, the `[[connections]]` section of the configuration
is ignored, and the relayer will instead discover all existing channels between the chains
present in the configuration.

__Example__

To start the relayer in multi-paths mode, invoke the `start-multi` commands. Note that
it does not require any options.

```shell
hermes start-multi
```


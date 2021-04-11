# Packet Relaying
The `start` command can be used to send packet transactions triggered by IBC packet events that occur for a given channel. This is also referred to packet streaming.
A new channel can be established or an existing one can be specified.

```shell script
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

## Start with New Channel

Use the `start` command without flags to create new clients on `source` and `destination` chains, and new connection and new channel between the two chains.

> Reusing existing clients or connection is not possible with the current version. The port used by the channel is obtained from and must be specified in the configuration file.

### Example

```shell script
hermes start ibc-0 ibc-1
```

The relayer creates a new client on each chain and then established a new connection and a new channel using that connection. After that is enters a listen loop acting on packet events that occur on that channel.

## Start on Existing Channel

Use the `start` command and specify the source port and channel identifier of a channel that is already created and in open state on both chains.

### Example

```shell script
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

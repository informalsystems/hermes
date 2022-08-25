# Transactions

There are a number of simple commands that perform minimal validation, build and send IBC transactions.

The `tx` command provides the following sub-commands:

| CLI name               | Description                                                                                                     |
| ---------------------- | --------------------------------------------------------------------------------------------------------------- |
| `conn-init`            | [Initialize a connection (ConnectionOpenInit)](./connection.md#connection-init)                            |
| `conn-try`             | [Relay the connection attempt (ConnectionOpenTry)](./connection.md#connection-try)                         |
| `conn-ack`             | [Relay acknowledgment of a connection attempt (ConnectionOpenAck)](./connection.md#connection-ack)         |
| `conn-confirm`         | [Confirm opening of a connection (ConnectionOpenConfirm)](./connection.md#connection-confirm)              |
| `chan-open-init`       | [Initialize a channel (ChannelOpenInit)](./channel-open.md#channel-open-init)                              |
| `chan-open-try`        | [Relay the channel attempt (ChannelOpenTry)](./channel-open.md#channel-open-try)                           |
| `chan-open-ack`        | [Relay acknowledgment of a channel attempt (ChannelOpenAck)](./channel-open.md#channel-open-ack)           |
| `chan-open-confirm`    | [Confirm opening of a channel (ChannelOpenConfirm)](./channel-open.md#channel-open-close)                  |
| `chan-close-init`      | [Initiate the closing of a channel (ChannelCloseInit)](./channel-close.md#channel-close-init)              |
| `chan-close-confirm`   | [Confirm the closing of a channel (ChannelCloseConfirm)](./channel-close.md#channel-close-confirm)         |
| `ft-transfer`          | [Send a fungible token transfer test transaction (ICS20 MsgTransfer](./packet.md#fungible-token-transfer)  |
| `packet-recv`          | [Relay receive or timeout packets](./packet.md#relay-receive-and-timeout-packets)                          |
| `packet-ack`           | [Relay acknowledgment packets](./packet.md#relay-acknowledgment-packets)                                   |
| `upgrade-chain`        | [Send an IBC upgrade plan](./upgrade.md)

The main purpose of these commands is to support development and testing, and continuous integration. These CLIs take quite a few parameters and they are explained in the individual sub-sections.

At a high level, most commands follow this template:

```shell
hermes tx <ibc-message> <dst-chain-id> <src-chain-id> [-d <dst-obj-id> -s <src-obj-id>]*
```

In the command template above:

- `ibc-message` - identifies the "main" IBC message that is being sent, e.g. `conn-init`, `conn-try`, `chan-open-init`, etc. To ensure successful processing on the receiving chain, the majority of these commands build and send two messages: one `UpdateClient` message followed by the actual IBC message. These two messages are included in a single transaction. This is done for all IBC messages that include proofs collected from the source chain.

    The messages that do not require proofs are:
    - `MsgConnectionOpenInit` (`conn-open-init` command),
    - `MsgChannelOpenInit` (`chan-open-init` command),
    - `MsgChannelCloseInit` (`chan-close-init` command) and
    - `MsgTransfer` (`ft-transfer` command)

- `dst-chain-id` - is the identifier of the chain where the transaction will be sent.

- `src-chain-id` - is the identifier of the chain that is queried for the data that is included in the transaction, e.g. connection data, client proofs, etc. To ensure correct on-chain state, the relayer also queries the destination chain, however it does not include this information in the Tx to the destination chain.

- `dst-obj-id` - the identifier of an object on destination chain required by the message, e.g. the `client-id` associated with the connection on destination chain in connection messages. Or the `connection-id` in a `ConnOpenAck` message.

- `src-obj-id` - the identifier of an object on the source chain, required by the message, e.d. the `client-id` of the connection on source chain.

- More details about the `tx` commands can be found in the following sections:
     - [Connection](./connection.md)
     - [Channel Open](./channel-open.md)
     - [Channel Close](./channel-close.md)
     - [Packet](./packet.md)
     - [Upgrade](./upgrade.md)

## Usage

```shell
USAGE:
    hermes tx <SUBCOMMAND>

DESCRIPTION:
    Raw commands for sending transactions to a configured chain.

SUBCOMMANDS:
    help                Get usage information
    conn-init           Initialize a connection (ConnectionOpenInit)
    conn-try            Relay the connection attempt (ConnectionOpenTry)
    conn-ack            Relay acknowledgment of a connection attempt (ConnectionOpenAck)
    conn-confirm        Confirm opening of a connection (ConnectionOpenConfirm)
    chan-open-init      Initialize a channel (ChannelOpenInit)
    chan-open-try       Relay the channel attempt (ChannelOpenTry)
    chan-open-ack       Relay acknowledgment of a channel attempt (ChannelOpenAck)
    chan-open-confirm   Confirm opening of a channel (ChannelOpenConfirm)
    chan-close-init     Initiate the closing of a channel (ChannelCloseInit)
    chan-close-confirm  Confirm the closing of a channel (ChannelCloseConfirm)
    ft-transfer         Send a fungible token transfer test transaction (ICS20 MsgTransfer)
    packet-recv         Relay receive or timeout packets
    packet-ack          Relay acknowledgment packets
    upgrade-chain       Send an IBC upgrade plan
```

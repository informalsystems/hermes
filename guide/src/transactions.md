# Raw Transactions

There are a number of simple commands that perform minimal validation, build and send IBC transactions. These are the `tx raw` commands:

```shell script
USAGE:
    hermes tx raw <SUBCOMMAND>

DESCRIPTION:
    tx raw

SUBCOMMANDS:
    help       get usage information
    create-client Create a client for source chain on destination chain
    update-client Update the specified client on destination chain
    conn-init  Initialize a connection (ConnectionOpenInit)
    conn-try   Relay the connection attempt (ConnectionOpenTry)
    conn-ack   Relay acknowledgment of a connection attempt (ConnectionOpenAck)
    conn-confirm Confirm opening of a connection (ConnectionOpenConfirm)
    chan-open-init Initialize a channel (ChannelOpenInit)
    chan-open-try Relay the channel attempt (ChannelOpenTry)
    chan-open-ack Relay acknowledgment of a channel attempt (ChannelOpenAck)
    chan-open-confirm Confirm opening of a channel (ChannelOpenConfirm)
    chan-close-init Initiate the closing of a channel (ChannelCloseInit)
    chan-close-confirm Confirm the closing of a channel (ChannelCloseConfirm)
    ft-transfer Send a fungible token transfer test transaction (ICS20 MsgTransfer)
    packet-recv Relay receive or timeout packets
    packet-ack Relay acknowledgment packets
```

The main purpose of these commands is to support development and testing, and continuous integration. These CLIs take quite a few parameters and they are explained in the individual sub-sections.

At a high level, most CLI has the following format/ usage:

```shell
   hermes tx raw <ibc-datagram> <dst-chain-id> <src-chain-id> [<dst-obj-id> <src-obj-id>]*
```

where:

- `ibc-datagram` - identifies the "main" IBC message that is being sent, e.g. conn-init, conn-try, chan-open-init, etc. To ensure successfull processing on the receiving chain, the majority of these commands build and send two messages: one `UpdateClient` message followed by the actual IBC message. These two messages are included in a single transaction. This is done for all IBC datagrams that include proofs collected from the source chain.

    The messages that do not require proofs are:
    - `MsgCreateClient` (`create-client` command),
    - `MsgConnectionOpenInit` (`conn-open-init` command),
    - `MsgChannelOpenInit` (`chan-open-init` command),
    - `MsgChannelCloseInit` (`chan-close-init` command) and
    - `MsgTransfer` (`ft-transfer` command)

- `dst-chain-id` - is the identifier of the chain where the transaction is sent.

- `src-chain-id` - is the identifier of the chain that is queried for the data that is included in the transaction, e.g. connection data, client proofs, etc. To ensure correct on-chain state, the relayer also queries the destination chain, however it does not include this information in the Tx to the destination chain.

- `dst-obj-id` - the identifier of an object on destination chain required by the datagram, e.g. the `client-id` associated with the connection on destination chain in connection datagrams. Or the `connection-id` in a `ConnOpenAck` datagram.

- `src-obj-id` - the identifier of an object on the source chain, required by the datagram, e.d. the `client-id` of the connection on source chain.

- More details about the `tx raw` commands can be found in the following sections:
     - [Client](./tx_client.md)
     - [Connection](./tx_connection.md)
     - [Channel](./tx_channel.md)
     - [Packet](./tx_packet.md)
# Path Setup and Relay Commands

This section describes a number of commands that can be used to manage clients, connections, channels and relay over new or existing  paths.

| CLI name               | Description                                                                                                     |
| ---------------------- | --------------------------------------------------------------------------------------------------------------- |
| `create client`        | [Create a client for source chain on destination chain](./clients.md#create-client)                         |
| `update client`        | [Update the specified client on destination chain](./clients.md#md-client)                              |
| `create connection`    | [Establish a connection using existing or new clients](./connections.md#establish-connection)                            |
| `create channel`       | [Establish a channel using existing or new connection](./channels.md#establish-channel)                            |
| `start`                | [Relay packets over a new or exsiting channel](./packets.md#start)                            |


## Create
Use the `create` commands to create a new clients, connections and channels.

```shell
USAGE:
    hermes create <SUBCOMMAND>

DESCRIPTION:
    Create objects (client, connection, or channel) on chains

SUBCOMMANDS:
    help       Get usage information
    client     Create a new IBC client
    connection Create a new connection between two chains
    channel    Create a new channel between two chains
```

## Update
Use the `update` commands to update a client.

```shell
USAGE:
    hermes update <SUBCOMMAND>

DESCRIPTION:
    Update objects (clients) on chains

SUBCOMMANDS:
    help       Get usage information
    client     Update an IBC client
```

## Relay 
Use the `start` commands to start relaying packets over one path.

```shell
USAGE:
    hermes start <OPTIONS>

DESCRIPTION:
    Start the relayer

POSITIONAL ARGUMENTS:
    src_chain_id              identifier of the source chain
    dst_chain_id              identifier of the destination chain

FLAGS:
    -p, --src-port-id SRC-PORT-ID
    -c, --src-channel-id SRC-CHANNEL-ID
```

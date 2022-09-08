# Path Setup

This section describes a number of commands that can be used to manage clients, connections, channels.

| CLI name               | Description                                                                                                     |
| ---------------------- | --------------------------------------------------------------------------------------------------------------- |
| `create client`        | [Create a client for source chain on destination chain](./clients.md#create-client)                         |
| `update client`        | [Update the specified client on destination chain](./clients.md#md-client)                              |
| `create connection`    | [Establish a connection using existing or new clients](./connections.md#establish-connection)                            |
| `create channel`       | [Establish a channel using a pre-existing connection, or alternatively create a new client and a new connection underlying the new channel](./channels.md#establish-channel)                            |


## Create
Use the `create` commands to create new clients, connections, and channels.

```shell
{{#template ../../../templates/commands/hermes/help/create.md}}
```

## Update
Use the `update` commands to update a client.

```shell
{{#template ../../../templates/commands/hermes/help/update.md}}
```

# Identifiers


A chain allocates identifiers when it creates clients, connections and channels. These identifiers can subsequently be used to refer to existing clients, connections and channels.

> NOTE: If you want to ensure you get the same identifiers while following the tutorials, run the each of the three commands below __once__ on `ibc-1`. This will ensure that when going through the tutorial, a second channel on `ibc-1` with identifier `channel-1` will created.

Chains allocate identifiers using a chain specific allocation scheme. Currently, *cosmos-sdk* implementation uses the follow identifiers:

### 1. Client Identifiers

__`07-tendermint-<n>`__ for tendermint clients

For example `07-tendermint-0` is assigned to the first client created on `ibc-1`:

 ```shell
hermes tx raw create-client ibc-1 ibc-0
 ```

 ```json
Success: CreateClient(
    CreateClient(
        Attributes {
            height: Height {
                revision: 1,
                height: 103,
            },
            client_id: ClientId(
                "07-tendermint-0",
            ),
            client_type: Tendermint,
            consensus_height: Height {
                revision: 0,
                height: 112,
            },
        },
    ),
)
 ```

We will create a second client on `ibc-1` with identifier `07-tendermint-1` in the client tutorial.

### 2. Connection Identifiers

__`connection-<n>`__ for connections

For example `connection-0` is assigned to the first connection created on `ibc-1`:

```shell
hermes tx raw conn-init ibc-1 ibc-0 07-tendermint-0 07-tendermint-0
```

```json
Success: OpenInitConnection(
    OpenInit(
        Attributes {
            height: Height {
                revision: 1,
                height: 119,
            },
            connection_id: Some(
                ConnectionId(
                    "connection-0",
                ),
            ),
            client_id: ClientId(
                "07-tendermint-0",
            ),
            counterparty_connection_id: None,
            counterparty_client_id: ClientId(
                "07-tendermint-0",
            ),
        },
    ),
)
```
We will create a second connection on `ibc-1` with identifier `connection-1` in the connection tutorial.

### 3. Channel Identifiers

`channel-<n>` for channels

For example `channel-0` is assigned to the first channel created on `ibc-1`:

```shell
hermes tx raw chan-open-init ibc-1 ibc-0 connection-0 transfer transfer
```

```json
Success: OpenInitChannel(
    OpenInit(
        Attributes {
            height: Height {
                revision: 1,
                height: 225,
            },
            port_id: PortId(
                "transfer",
            ),
            channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
            connection_id: ConnectionId(
                "connection-0",
            ),
            counterparty_port_id: PortId(
                "transfer",
            ),
            counterparty_channel_id: None,
        },
    ),
)
```

In the following tutorials the __`ibc-0`__ and __`ibc-1`__ chains are setup and configured. 

For clarity, the tutorials run on a setup where the identifiers allocated to the client, connection and channel on __`ibc-0`__ are __`07-tendermint-0`__, __`connection-0`__ and __`channel-0`__ respectively. Identifiers allocated to the client, connection and channel on __`ibc-1`__ are __`07-tendermint-1`__, __`connection-1`__ and __`channel-1`__ respectively.

Before going over the next sections, please ensure the commands above are executed.

### Next Steps

The following sections describe the commands to connect and relay packets between two chains. You can:

1. use a [simplified approach](./relay-paths/index.md) for managing relaying paths, or
2. use [individual (raw) transactions](./raw/index.md) to create
   all the necessary chain objects (clients, connections, channels) and relay packets.


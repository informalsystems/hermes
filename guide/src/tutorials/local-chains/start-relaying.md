# Start relaying

A relay path refers to a specific channel used to interconnect two chains and over which packets are being sent.

Hermes can be started to listen for packet events on the two ends of multiple paths and relay packets over these paths.
This can be done over a new path or over existing paths.

>__WARNING__ Before proceeding to the sections above, please first, make sure you followed the steps in the [Identifiers section](../identifiers.md)


## Create a new path

Perform client creation, connection and channel handshake to establish a new path between the `transfer` ports on `ibc-0` and `ibc-1` chains.

```shell
hermes create channel --a-chain ibc-0 --b-chain ibc-1 --a-port transfer --b-port transfer --new-client-connection
```

If all the handshakes are performed successfully you should see a message similar to the one below:

```json
Success: Channel {
    ordering: Unordered,
    a_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-0",
                version: 0,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-0",
        ),
        connection_id: ConnectionId(
            "connection-0",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-0",
        ),
    },
    b_side: ChannelSide {
        chain: ProdChainHandle {
            chain_id: ChainId {
                id: "ibc-1",
                version: 1,
            },
            runtime_sender: Sender { .. },
        },
        client_id: ClientId(
            "07-tendermint-1",
        ),
        connection_id: ConnectionId(
            "connection-1",
        ),
        port_id: PortId(
            "transfer",
        ),
        channel_id: ChannelId(
            "channel-1",
        ),
    },
    connection_delay: 0s,
    version: Some(
        "ics20-1",
    ),
}

```

Note that for each side, *a_side* (__ibc-0__) and *b_side* (__ibc-1__) there are a __client_id__, __connection_id__, __channel_id__ and __port_id__.
With all these established, you have a path that you can relay packets over.

Visualize the current network with 

```bash
hermes query channels --chain ibc-1 --show-counterparty
```

If all the commands were successful, this command should output : 

```
ibc-1: transfer/channel-0 --- ibc-0: transfer/None
ibc-1: transfer/channel-1 --- ibc-0: transfer/channel-0
```

The first line represents the dummy channel opened in section [Identifiers](./identifiers.md) for which the handshake was never completed. The second represents the path you created in this section.

## Start relaying

- Open a new terminal and start Hermes using the `start` command : 

```bash
hermes start
```
Hermes will first relay the pending packets that have not been relayed and then start passive relaying by listening to and acting on packet events. 

- In a separate terminal, use the `ft-transfer` command to send:
    - Two packets from ibc-0 to ibc-1 from channel-0
    ```bash
        hermes tx ft-transfer --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-channel channel-0 --amount 9999 --timeout-seconds 1000 --number-msgs 2
    ```
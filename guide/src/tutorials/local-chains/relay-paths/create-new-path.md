# Create a new path

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
With all these established, you have [a path that you can relay packets over](./multiple-paths.md).

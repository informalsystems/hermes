# Concurrent packet relaying on multiple paths 
At the moment, the `start` command relays packets over a single channel.
To relay packets over multiple channels, one can instead use the `start-multi` command.

> __WARINING__: Relaying packets concurrently over multiple channels with the
> `start-multi` command is currently __experimental__. Use at your own risk.

1. Paste the following configuration in a file named `config.toml`:

    ```toml
    [global]
    strategy = 'naive'
    log_level = 'error'

    [[chains]]
    id = 'ibc-0'
    rpc_addr = 'http://localhost:26657'
    grpc_addr = 'http://localhost:9090'
    websocket_addr = 'ws://localhost:26657/websocket'
    rpc_timeout = '10s'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    gas = 200000
    fee_denom = 'stake'
    fee_amount = 10
    clock_drift = '5s'
    trusting_period = '14days'

    [chains.trust_threshold]
    numerator = '1'
    denominator = '3'

    [[chains]]
    id = 'ibc-1'
    rpc_addr = 'http://localhost:26557'
    grpc_addr = 'http://localhost:9091'
    websocket_addr = 'ws://localhost:26557/websocket'
    rpc_timeout = '10s'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    gas = 200000
    fee_denom = 'stake'
    fee_amount = 10
    clock_drift = '5s'
    trusting_period = '14days'

    [chains.trust_threshold]
    numerator = '1'
    denominator = '3'

    [[connections]]
    a_chain = 'ibc-0'
    b_chain = 'ibc-1'

    [[connections.paths]]
    a_port = 'transfer'
    b_port = 'transfer'

    [[connections]]
    a_chain = 'ibc-1'
    b_chain = 'ibc-2'

    [[connections.paths]]
    a_port = 'transfer'
    b_port = 'transfer'
    ```

2. Run the `dev-env` script with the parameters below to start three chains:

    ```bash
    ./scripts/dev-env config.toml ibc-0 ibc-1 ibc-2
    ```

    > __NOTE__: If the script above prompts you to delete the data folder, answer __'yes'__.

    The script configures and starts three __`gaiad`__ instances, named __`ibc-0`__, and __`ibc-1`__, and __`ibc-2`__.

4. Create a channel between `ibc-0` and `ibc-1`:

    ```shell
    hermes -c config.toml create channel ibc-0 ibc-1 --port-a transfer --port-b transfer -o unordered
    ```

    ```rust
    (...)

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
        connection_delay: 0ns,
        version: Some(
            "ics20-1",
        ),
    }
    ```

    Note that the channel identifier on both `ibc-0` and `ibc-1` is `channel-0`.

5. Create a channel between `ibc-1` and `ibc-2`:

    ```shell
    hermes -c config.toml create channel ibc-1 ibc-2 --port-a transfer --port-b transfer -o unordered
    ```

    ```rust
    (...)

    Success: Channel {
        ordering: Unordered,
        a_side: ChannelSide {
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
        b_side: ChannelSide {
            chain: ProdChainHandle {
                chain_id: ChainId {
                    id: "ibc-2",
                    version: 2,
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
        connection_delay: 0ns,
        version: Some(
            "ics20-1",
        ),
    }
    ```

    Note that the channel identifier on `ibc-1` is `channel-1`, and on `ibc-2` it is `channel-0`.

3. From a terminal, start Hermes using the `start-multi` command:

    ```shell
    hermes -c config.toml start-multi
    ```

4. In a separate terminal, use the `ft-transfer` command to send:

    - two packets from `ibc-0` to `ibc-1` from source channel `channel-0`
    - two packets from `ibc-1` to `ibc-2` from source channel `channel-1`

    ```shell
    hermes -c config.toml tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 1000 -n 2
    hermes -c config.toml tx raw ft-transfer ibc-1 ibc-2 transfer channel-1 9999 1000 -n 2
    ```

5. Observe the output on the relayer terminal, verify that the send events are processed, and that the `recv_packet`s are sent out.

5. Query the unreceived packets on `ibc-1` and `ibc-2` from a different terminal:

    ```shell
    hermes -c config.toml query packet unreceived-packets ibc-1 ibc-0 transfer channel-0
    hermes -c config.toml query packet unreceived-acks    ibc-0 ibc-1 transfer channel-1
    hermes -c config.toml query packet unreceived-packets ibc-0 ibc-1 transfer channel-1
    hermes -c config.toml query packet unreceived-acks    ibc-1 ibc-0 transfer channel-0
    ```


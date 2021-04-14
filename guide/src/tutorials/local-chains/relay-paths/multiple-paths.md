# Concurrent packet relaying on multiple paths

At the moment, the `start` command relays packets over a single channel.
To relay packets over multiple channels concurrently, one can instead use
the `start-multi` command.

> __WARNING__: Relaying packets concurrently over multiple channels with the
> `start-multi` command is currently __experimental__. Use at your own risk.

> __Caveat__: At the moment, `start-multi` does not clear pending packets
> when starting. It is therefore advised to only use it for channels which
> do not have pending packets.

1. Paste the following configuration in a file named __`multi-config.toml`__:

    ```toml
    [global]
    strategy = 'naive'
    log_level = 'info'

    [[chains]]
    id = 'ibc-0'
    rpc_addr = 'http://127.0.0.1:26657'
    grpc_addr = 'http://127.0.0.1:9090'
    websocket_addr = 'ws://127.0.0.1:26657/websocket'
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
    rpc_addr = 'http://127.0.0.1:26557'
    grpc_addr = 'http://127.0.0.1:9091'
    websocket_addr = 'ws://127.0.0.1:26557/websocket'
    rpc_timeout = '10s'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    gas = 200000
    fee_denom = 'stake'
    fee_amount = 10
    clock_drift = '5s'
    trusting_period = '14days'

    [[chains]]
    id = 'ibc-2'
    rpc_addr = 'http://127.0.0.1:26457'
    grpc_addr = 'http://127.0.0.1:9092'
    websocket_addr = 'ws://127.0.0.1:26457/websocket'
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

    This configuration three chains `ibc-0`, `ibc-1` and `ibc-2` as well
    as two connections: one between `ibc-0` and `ibc-1`, and another
    between `ibc-1` and `ibc-2`, both using the `transfer` ports.

2. Run the `dev-env` script with the parameters below to start three chains:

    ```bash
    ./scripts/dev-env multi-config.toml ibc-0 ibc-1 ibc-2
    ```

    > __NOTE__: If the script above prompts you to delete the data folder, answer __'yes'__.

    The script configures and starts three __`gaiad`__ instances, named __`ibc-0`__, and __`ibc-1`__, and __`ibc-2`__.


3. Create a channel between `ibc-0` and `ibc-1`:

    ```shell
    hermes -c multi-config.toml create channel ibc-0 ibc-1 --port-a transfer --port-b transfer -o unordered
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
    hermes -c multi-config.toml create channel ibc-1 ibc-2 --port-a transfer --port-b transfer -o unordered
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
    hermes -c multi-config.toml start-multi
    ```

4. In a separate terminal, use the `ft-transfer` command to send:

    - two packets from `ibc-0` to `ibc-1` from source channel `channel-0`

      ```shell
      hermes -c multi-config.toml tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 1000 -n 2
      ```

      ```rust
      Success: [
          SendPacket(
              SendPacket {
                  height: revision: 0, height: 3056,
                  packet: PortId("transfer") ChannelId("channel-0") Sequence(3),
              },
          ),
          SendPacket(
              SendPacket {
                  height: revision: 0, height: 3056,
                  packet: PortId("transfer") ChannelId("channel-0") Sequence(4),
              },
          ),
      ]
      ```

    - two packets from `ibc-1` to `ibc-2` from source channel `channel-1`

      ```shell
      hermes -c multi-config.toml tx raw ft-transfer ibc-2 ibc-1 transfer channel-1 9999 1000 -n 2
      ```

      ```rust
      Success: [
          SendPacket(
              SendPacket {
                  height: revision: 1, height: 3076,
                  packet: PortId("transfer") ChannelId("channel-1") Sequence(3),
              },
          ),
          SendPacket(
              SendPacket {
                  height: revision: 1, height: 3076,
                  packet: PortId("transfer") ChannelId("channel-1") Sequence(4),
              },
          ),
      ]
      ```

5. Observe the output on the relayer terminal, verify that the send events are processed, and that the `recv_packets` are sent out.

    ```
    (...)

    INFO ibc_relayer::link: [ibc-0 -> ibc-1] result events:
        UpdateClientEv(ev_h:1-3048, 07-tendermint-0(0-3057), )
        WriteAcknowledgementEv(h:1-3048, seq:3, path:channel-0/transfer->channel-0/transfer, toh:1-4045, tos:0))
        WriteAcknowledgementEv(h:1-3048, seq:4, path:channel-0/transfer->channel-0/transfer, toh:1-4045, tos:0))
    INFO ibc_relayer::link: [ibc-0 -> ibc-1] success

    (...)

    INFO ibc_relayer::link: [ibc-1 -> ibc-0] clearing old packets
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] received from query_txs []
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] finished clearing pending packets
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] generate messages from batch with 2 events
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] scheduling op. data with 2 msg(s) for Destination chain (height 1-3049)
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] relay op. data to Destination, proofs height 1-3048, (delayed by: 2.154603ms) [try 1/10]
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] prepending Destination client update @ height 1-3049
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] assembled batch of 3 message(s)
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] result events:
        UpdateClientEv(ev_h:0-3059, 07-tendermint-0(1-3049), )
        AcknowledgePacketEv(h:0-3059, seq:3, path:channel-0/transfer->channel-0/transfer, toh:1-4045, tos:0))
        AcknowledgePacketEv(h:0-3059, seq:4, path:channel-0/transfer->channel-0/transfer, toh:1-4045, tos:0))
    INFO ibc_relayer::link: [ibc-1 -> ibc-0] success

    (...)
    ```

5. Query the unreceived packets and acknowledgments on `ibc-1` and `ibc-2` from a different terminal:

    ```shell
    hermes -c multi-config.toml query packet unreceived-packets ibc-1 ibc-0 transfer channel-0
    hermes -c multi-config.toml query packet unreceived-acks    ibc-0 ibc-1 transfer channel-1
    hermes -c multi-config.toml query packet unreceived-packets ibc-0 ibc-1 transfer channel-1
    hermes -c multi-config.toml query packet unreceived-acks    ibc-1 ibc-0 transfer channel-0
    ```

    If everything went well, each of these commands should result in:

    ```
    Success: []
    ```

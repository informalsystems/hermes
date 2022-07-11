# Relay packets on multiple paths

Hermes can relay packets over all current or future paths between the configured set of chains.

Follow the steps below to connect three chains together and relay packets between them:

1. Add the config for the third chain to the existing `$HOME/.gm/gm.toml` file

    ```toml
    [global]
    add_to_hermes = false
    auto_maintain_config = true
    extra_wallets = 2
    gaiad_binary = "~/go/bin/gaiad"
    hdpath = ""
    home_dir = "$HOME/.gm"
    ports_start_at = 27000
    validator_mnemonic = ""
    wallet_mnemonic = ""

    [global.hermes]
        binary = "$HOME/ibc-rs/target/debug/hermes" #change this path according to your setup
        config = "./hermes"
        log_level = "info"
        telemetry_enabled = true
        telemetry_host = "127.0.0.1"
        telemetry_port = 3001

    [ibc-0]
    ports_start_at = 27010

    [ibc-1]
    ports_start_at = 27020

    [node-0]
    add_to_hermes = true
    network = "ibc-0"
    ports_start_at = 27030

    [node-1]
    add_to_hermes = true
    network = "ibc-1"
    ports_start_at = 27040

    [ibc-2]
    ports_start_at = 27050

    [node-2]
    add_to_hermes = true
    network = "ibc-2"
    ports_start_at = 27060

    ```

2. Start the third chain

    ```bash
    gm start
    ```
3. Update the `$HOME/.hermes/.config.toml` file

    ```bash
    gm hermes config
    ```
4. Associate the keys to the new chain

    ```bash
    gm hermes keys
    ```
5. Check the status of the chains

    ```bash
    gm status
    ```

6. Create a channel between `ibc-0` and `ibc-1`. Since this is the first time
   we're connecting these two chains, we'll need to spin up a client and a
   connection between them as well. The `create channel` command gives us the
   convenient option to create a client and a connection. Keep in mind that this
   is not the default behavior of `create channel`, but in this case we're
   making an exception. Execute the following command:

    ```shell
    hermes create channel ibc-0 --chain-b ibc-1 --port-a transfer --port-b transfer --new-client-connection
    ```

    Then respond 'yes' to the prompt that pops up. Once the command has run to
    completion, you should see the following among the output logs:

    ```json
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
        connection_delay: 0s,
        version: Some(
            "ics20-1",
        ),
    }
    ```

    Note that the channel identifier on both `ibc-0` and `ibc-1` is `channel-0`.

7. Create a channel between `ibc-1` and `ibc-2` using the structure of the
   previous invocation we used to create a channel between `ibc-0` and `ibc-1`:

    ```shell
    hermes create channel ibc-1 --chain-b ibc-2 --port-a transfer --port-b transfer --new-client-connection
    ```

    ```json
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
        connection_delay: 0s,
        version: Some(
            "ics20-1",
        ),
    }
    ```

    Note that the channel identifier on `ibc-1` is `channel-1`, and on `ibc-2` it is `channel-0`.

8. Start Hermes using the `start` command:

    ```shell
    hermes start
    ```

   Hermes will first relay the pending packets that have not been relayed and then
   start passive relaying by listening to and acting on packet events.

9. In a separate terminal, use the `ft-transfer` command to send:

    - Two packets from `ibc-0` to `ibc-1` from source channel `channel-0`

      ```shell
      hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 -o 1000 -n 2
      ```

      ```json
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

    - Two packets from `ibc-1` to `ibc-2` from source channel `channel-1`

      ```shell
      hermes tx raw ft-transfer ibc-2 ibc-1 transfer channel-1 9999 -o 1000 -n 2
      ```

      ```json
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

10. Observe the output on the relayer terminal, verify that the send events are processed, and that the `recv_packets` are sent out.

    ```text
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

11. Query the unreceived packets and acknowledgments on `ibc-1` and `ibc-2` from a different terminal:

    ```shell
    hermes query packet unreceived-packets ibc-1 transfer channel-0
    hermes query packet unreceived-acks ibc-0 transfer channel-0
    hermes query packet unreceived-packets ibc-2 transfer channel-0
    hermes query packet unreceived-acks ibc-1 transfer channel-1
    ```

    If everything went well, each of these commands should result in:

    ```
    Success: []
    ```

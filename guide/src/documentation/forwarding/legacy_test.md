# Testing Packet Forwarding

## Prerequisites

- Gaiad `(v6.*.*)`. The version can be checked with:

```shell
gaiad version --log_level error --long | head -n4
```

## Testing procedure

### Setup using Gaia manager
> Note: The `gm.toml` file that we're using here looks like this:
```
[global]
  add_to_hermes = true
  auto_maintain_config = true
  extra_wallets = 2
  gaiad_binary = "/Users/luca/go/bin/gaiad"
  hdpath = ""
  home_dir = "/Users/luca/.gm"
  ports_start_at = 27000
  validator_mnemonic = ""
  wallet_mnemonic = ""

  [global.hermes]
    binary = "$HOME/.hermes/bin/hermes"
    config = "$HOME/.hermes/config.toml"
    log_level = "trace"
    telemetry_enabled = true
    telemetry_host = "127.0.0.1"
    telemetry_port = 3001

[ibc-0]
  ports_start_at = 27000

[ibc-1]
  ports_start_at = 27010

[ibc-2]
  ports_start_at = 27020
```
* Run the command `{{#template ../../templates/commands/gm/start.md}}`
* Run the commands: `{{#template ../../templates/commands/gm/hermes_config.md}}` and `{{#template ../../templates/commands/gm/hermes_keys.md}}`

### Test packet forwarding

1. Create a channel between `ibc-0` and `ibc-1`, and another between `ibc-1` and `ibc-2`:

    ```shell
    {{#template ../../templates/commands/hermes/create/channel_2.md A_CHAIN_ID=ibc-0 B_CHAIN_ID=ibc-1 A_PORT_ID=transfer B_PORT_ID=transfer}}
    ```

    ```json
    SUCCESS Channel {
        ordering: Unordered,
        a_side: ChannelSide {
            chain: BaseChainHandle {
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
            channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
            version: None,
        },
        b_side: ChannelSide {
            chain: BaseChainHandle {
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
            channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
            version: None,
        },
        connection_delay: 0ns,
    }
    ```

    ```shell
    {{#template ../../templates/commands/hermes/create/channel_2.md A_CHAIN_ID=ibc-1 B_CHAIN_ID=ibc-2 A_PORT_ID=transfer B_PORT_ID=transfer}}
    ```

    ```json
    SUCCESS Channel {
        ordering: Unordered,
        a_side: ChannelSide {
            chain: BaseChainHandle {
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
            channel_id: Some(
                ChannelId(
                    "channel-1",
                ),
            ),
            version: None,
        },
        b_side: ChannelSide {
            chain: BaseChainHandle {
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
            channel_id: Some(
                ChannelId(
                    "channel-0",
                ),
            ),
            version: None,
        },
        connection_delay: 0ns,
    }
    ```

2. Obtain the addresses of the wallets on each chain:

    ```shell
    {{#template ../../templates/commands/hermes/keys/list_1.md CHAIN_ID=ibc-0}}
    ```

    ```json
    SUCCESS 
    - wallet2 (cosmos179ld56nmany7nqmsdjz684rx5t4r5gxspn6hgr)
    - wallet (cosmos1gz507egejvz3ukg3xwr3v04n3xcny7vcnkjw32)
    - wallet1 (cosmos14cgtalvczzm6xuaa086g5tx6sss6e85j55vqrd)
    ```

    ```shell
    {{#template ../../templates/commands/hermes/keys/list_1.md CHAIN_ID=ibc-1}}
    ```

    ```json
    SUCCESS 
    - wallet2 (cosmos1pmzq62tewxla9z7gpntcnvszyrkygnk4mesauy)
    - wallet (cosmos1jwr34yvnkqkc0ddndnh9y8t94hlhn7rapfyags)
    - wallet1 (cosmos1at4nj238c3ltlj0wymwgfjmdjctlvstwj8xl2s)
    ```

    ```shell
    {{#template ../../templates/commands/hermes/keys/list_1.md CHAIN_ID=ibc-2}}
    ```

    ```json
    SUCCESS 
    - wallet2 (cosmos1xpezl2vvwg9fhdmksvne6lygd7dwz4vf65v6ye)
    - wallet (cosmos1nsztzzhl553avufxhqa204908l4dndafqph4tw)
    - wallet1 (cosmos1csdnmydggcyvjd7z8l64z9lpdgmgyr4v7hw5r8)
    ```

3. (Optional) Check the balance of the wallets before transfering tokens:

    ```shell
    {{#template ../../templates/commands/hermes/keys/balance_1.md CHAIN_ID=ibc-0 OPTIONS= --all}}
    ```

    ```json
    SUCCESS Balances for key `wallet`:
            100000000 samoleans
            99992294 stake
    ```

    ```shell
    {{#template ../../templates/commands/hermes/keys/balance_1.md CHAIN_ID=ibc-1 OPTIONS= --all}}
    ```

    ```json
    SUCCESS Balances for key `wallet`:
            100000000 samoleans
            99983377 stake
    ```

    ```shell
    {{#template ../../templates/commands/hermes/keys/balance_1.md CHAIN_ID=ibc-2 OPTIONS= --all}}
    ```

    ```json
    SUCCESS Balances for key `wallet`:
            100000000 samoleans
            99990916 stake
    ```

4. (Optional) Confirm the name of the channels used for the transfer:

    ```shell
    {{#template ../../templates/commands/hermes/query/channels_1.md CHAIN_ID=ibc-0 OPTIONS= --counterparty-chain ibc-1}}
    ```

    ```json
    SUCCESS [
        PortChannelId {
            channel_id: ChannelId(
                "channel-0",
            ),
            port_id: PortId(
                "transfer",
            ),
        },
    ]
    ```

    ```shell
    {{#template ../../templates/commands/hermes/query/channels_1.md CHAIN_ID=ibc-1 OPTIONS= --counterparty-chain ibc-2}}
    ```

    ```json
    SUCCESS [
        PortChannelId {
            channel_id: ChannelId(
                "channel-1",
            ),
            port_id: PortId(
                "transfer",
            ),
        },
    ]
    ```

5. In a separate terminal, start an instance of Hermes:

    ```shell
    {{#template ../../templates/commands/hermes/start_1.md}}
    ```

6. Transfer token using the special receiver:

    ```shell
    {{#template ../../templates/commands/hermes/tx/ft-transfer_1.md DST_CHAIN_ID=ibc-1 SRC_CHAIN_ID=ibc-0 SRC_PORT_ID=transfer SRC_CHANNEL_ID=channel-0 AMOUNT=2500 OPTIONS= --denom samoleans --receiver 'cosmos1jwr34yvnkqkc0ddndnh9y8t94hlhn7rapfyags|transfer/channel-1:cosmos1nsztzzhl553avufxhqa204908l4dndafqph4tw' --timeout-seconds 120}}
    ```

    ```json
    SUCCESS [
        IbcEventWithHeight {
            event: SendPacket(
                SendPacket {
                    packet: Packet {
                        sequence: Sequence(
                            2,
                        ),
                        source_port: PortId(
                            "transfer",
                        ),
                        source_channel: ChannelId(
                            "channel-0",
                        ),
                        destination_port: PortId(
                            "transfer",
                        ),
                        destination_channel: ChannelId(
                            "channel-0",
                        ),
                        data: [123, 34, 97, 109, 111, 117, 110, 116, 34, 58, 34, 50, 53, 48, 48, 34, 44, 34, 100, 101, 110, 111, 109, 34, 58, 34, 115, 97, 109, 111, 108, 101, 97, 110, 115, 34, 44, 34, 114, 101, 99, 101, 105, 118, 101, 114, 34, 58, 34, 99, 111, 115, 109, 111, 115, 49, 106, 119, 114, 51, 52, 121, 118, 110, 107, 113, 107, 99, 48, 100, 100, 110, 100, 110, 104, 57, 121, 56, 116, 57, 52, 104, 108, 104, 110, 55, 114, 97, 112, 102, 121, 97, 103, 115, 124, 116, 114, 97, 110, 115, 102, 101, 114, 47, 99, 104, 97, 110, 110, 101, 108, 45, 49, 58, 99, 111, 115, 109, 111, 115, 49, 110, 115, 122, 116, 122, 122, 104, 108, 53, 53, 51, 97, 118, 117, 102, 120, 104, 113, 97, 50, 48, 52, 57, 48, 56, 108, 52, 100, 110, 100, 97, 102, 113, 112, 104, 52, 116, 120, 34, 44, 34, 115, 101, 110, 100, 101, 114, 34, 58, 34, 99, 111, 115, 109, 111, 115, 49, 103, 122, 53, 48, 55, 101, 103, 101, 106, 118, 122, 51, 117, 107, 103, 51, 120, 119, 114, 51, 118, 48, 52, 110, 51, 120, 99, 110, 121, 55, 118, 99, 110, 107, 106, 119, 51, 50, 34, 125],
                        timeout_height: Never,
                        timeout_timestamp: Timestamp {
                            time: Some(
                                Time(
                                    2022-11-10 16:05:13.409228,
                                ),
                            ),
                        },
                    },
                },
            ),
            height: Height {
                revision: 0,
                height: 59,
            },
        },
    ]
    ```

7. (Optional) Check the balances:

    ```shell
    {{#template ../../templates/commands/hermes/keys/balance_1.md CHAIN_ID=ibc-0 OPTIONS= --all}}
    ```

    ```json
    SUCCESS Balances for key `wallet`:
            99997500 samoleans
            99985136 stake
    ```

    ```shell
    {{#template ../../templates/commands/hermes/keys/balance_1.md CHAIN_ID=ibc-1 OPTIONS= --all}}
    ```

    ```json
    SUCCESS Balances for key `wallet`:
            100000000 samoleans
            99972551 stake
    ```

    ```shell
    {{#template ../../templates/commands/hermes/keys/balance_1.md CHAIN_ID=ibc-2 OPTIONS= --all}}
    ```

    ```json
    SUCCESS Balances for key `wallet`:
            2500 ibc/F47F0D7C9B4F7D971DF647A75A80CB8D905D3230262FEF2996340664D3A12D48
            100000000 samoleans
            99987055 stake
    ```
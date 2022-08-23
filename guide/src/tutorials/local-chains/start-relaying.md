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

Visualize the current network with: 

```shell
hermes query channels --chain ibc-1 --show-counterparty
```

If all the commands were successful, this command should output : 

```
ibc-1: transfer/channel-0 --- ibc-0: transfer/None
ibc-1: transfer/channel-1 --- ibc-0: transfer/channel-0
```

The first line represents the dummy channel opened in section [Identifiers](./identifiers.md) for which the handshake was never completed. The second represents the path you created in this section.

## Query balances

The commands to query balances are:

- for ibc-0:

    ```shell
    gaiad --node tcp://localhost:27030 query bank balances $(gaiad --home ~/.gm/ibc-0 keys --keyring-backend="test" show wallet -a)
    ```

- for ibc-1:

    ```shell
    gaiad --node tcp://localhost:27040 query bank balances $(gaiad --home ~/.gm/ibc-1 keys --keyring-backend="test" show wallet -a)
    ```

> __NOTE__ the RPC addresses used in the two commands above are configured in `~/.hermes/config.toml` file. It can also be found with `gm status`

At this point of the tutorial, the two commands should output something similar to:

```
- amount: "100000000"
  denom: samoleans
- amount: "99994088"
  denom: stake
pagination:
  next_key: null
  total: "0"
```

## Start relaying

Now, let's exchange `samoleans` between two chains.

- Open a new terminal and start Hermes using the `start` command : 

    ```shell
    hermes start
    ```
    Hermes will first relay the pending packets that have not been relayed and then start passive relaying by listening to and acting on packet events. 

- In a separate terminal, use the `ft-transfer` command to send `100000 samoleans` from ibc-0 to ibc-1 from channel-0:
    ```shell
        hermes tx ft-transfer --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-channel channel-0 --amount 100000 --timeout-seconds 1000
    ```
- Wait a few seconds then query balances on `ibc-1` and `ibc-0`. You should observe something similar to:
    - ibc-0:
        ```
            - amount: "99900000"
            denom: samoleans
            - amount: "99992054"
            denom: stake
            pagination:
            next_key: null
            total: "0"
        ```
    - ibc-1:
        ```
            - amount: "100000"
            denom: ibc/C1840BD16FCFA8F421DAA0DAAB08B9C323FC7685D0D7951DC37B3F9ECB08A199
            - amount: "100000000"
            denom: samoleans
            - amount: "99989196"
            denom: stake
            pagination:
            next_key: null
            total: "0"
        ```
    The samoleans were transfered to ibc-1 and are visible under the denom `ibc/C1840...`. 

- Transfer back `50000` these tokens to ibc-0:
    ```shell
        hermes tx ft-transfer --dst-chain ibc-0 --src-chain ibc-1 --src-port transfer --src-channel channel-1 --amount 50000 --timeout-seconds 1000 --denom ibc/C1840BD16FCFA8F421DAA0DAAB08B9C323FC7685D0D7951DC37B3F9ECB08A199
    ```
- Wait a few seconds then query balances on `ibc-1` and `ibc-0` again. You should observe something similar to:
    - ibc-0:
        ```
            - amount: "100000000"
            denom: samoleans
            - amount: "99987927"
            denom: stake
            pagination:
            next_key: null
            total: "0"
        ```
    - ibc-1:
        ```
            - amount: "0"
            denom: ibc/C1840BD16FCFA8F421DAA0DAAB08B9C323FC7685D0D7951DC37B3F9ECB08A199
            - amount: "100000000"
            denom: samoleans
            - amount: "99983879"
            denom: stake
            pagination:
            next_key: null
            total: "0"
        ```
- Open your browser and open `http://localhost:3001/metrics`. At this point, you should observe that the `wallet_balance` metric corresponds to what you observed in the previous step. All the metrics can be useful and are described in the [Telemetry](../../documentation/telemetry/index.md) section. We will describe a way to use them in the tutorial [Relaying in production](../production/index.md).

## Stop relaying and stop the chains

- Stop Hermes by pressing `Ctrl+C` on the terminal running `hermes start`.

- Stop the chains with `gm stop`.
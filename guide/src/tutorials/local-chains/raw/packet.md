# 4. Relay Packets

### 4.1 Query balances

- balance at ibc-0

    ```shell
    gaiad --node tcp://localhost:27010 query bank balances $(gaiad --home ~/.gm/ibc-0 keys --keyring-backend="test" show wallet -a)
    ```

- balance at ibc-1

    ```shell
    gaiad --node tcp://localhost:27020 query bank balances $(gaiad --home ~/.gm/ibc-1 keys --keyring-backend="test" show wallet -a)
    ```

> Note that the RPC addresses used in the two commands above are configured in `~/.hermes/config.toml` file. It can also be found with `gm status`

### 4.2 Packet relaying

First, we'll send `9999` `samoleans` from `ibc-0` to `ibc-1`.

- start the transfer of 9999 samoleans from `ibc-0` to `ibc-1`. This sends a `MsgTransfer` in a transaction to `ibc-0`

    ```shell
    hermes tx ft-transfer --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0 --amout 9999 --timeout-height-offset 1000 --number-msgs 1 --denom samoleans
    ```

- query packet commitments on `ibc-0`

    ```shell
    hermes query packet commitments --chain ibc-0 --port transfer --channel channel-0
    ```

- query pending packets on `ibc-1`

    ```shell
    hermes query packet pending-sends --chain ibc-1 --port transfer --channel channel-1
    ```

- send `recv_packet` to `ibc-1`

    ```shell
    hermes tx packet-recv --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0
    ```

- query pending acks on `ibc-0`

    ```shell
    hermes query packet pending-acks --chain ibc-0 --port transfer --channel channel-0
    ```

- send acknowledgement to `ibc-0`

    ```shell
    hermes tx packet-ack --receiver-chain ibc-0 --sender-chain ibc-1 --sender-port transfer --sender-channel channel-1
    ```

Send those samoleans back, from `ibc-1` to `ibc-0`.

```shell
hermes tx ft-transfer --receiver-chain ibc-0 --sender-chain ibc-1 --sender-port transfer --sender-channel channel-1 --amount 9999 --timeout-height-offset 1000 --number-msgs 1 --denom ibc/49D321B40FCF56B0370E5673CF090389C8E9CD185209FBE1BEE5D94E58E69BDC
hermes tx packet-recv --receiver-chain ibc-0 --sender-chain ibc-1 --sender-port transfer --sender-channel channel-1
hermes tx packet-ack --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0
```

The `ibc/49D321B40FCF56B0370E5673CF090389C8E9CD185209FBE1BEE5D94E58E69BDC` denominator above can be obtained by querying the balance at `ibc-1` after the transfer from `ibc-0` to `ibc-1` is concluded.

Next we will test the packet timeouts.
- send 1 packet with low timeout height offset to ibc-0

    ```shell
    hermes tx ft-transfer --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0 --amount 9999 --timeout-height-offset 2 --number-msgs 1
    ```

- send timeout to `ibc-0`

    ```shell
    hermes tx packet-recv --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0
    ```

- send 1 packet with 2 second timeout to ibc-0

    ```shell
    hermes tx ft-transfer --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0 --amount 9999 --timeout-seconds 2 --number-msgs 1
    ```

- send timeout to `ibc-0`

    ```shell
    hermes tx packet-recv --receiver-chain ibc-1 --sender-chain ibc-0 --sender-port transfer --sender-channel channel-0
    ```

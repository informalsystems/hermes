# 4. Relay Packets

### 4.1 Query balances

- balance at ibc-0

    ```shell
    gaiad --node tcp://localhost:26657 query bank balances $(gaiad --home data/ibc-0 keys --keyring-backend="test" show user -a)
    ```

- balance at ibc-1

    ```shell
    gaiad --node tcp://localhost:26557 query bank balances $(gaiad --home data/ibc-1 keys --keyring-backend="test" show user -a)
    ```

> Note that the addresses used in the two commands above are configured in `dev-env`.

### 4.2 Packet relaying

First, we'll send `9999` `samoleans` from `ibc-0` to `ibc-1`.

- start the transfer of 9999 samoleans from `ibc-0` to `ibc-1`. This sends a `MsgTransfer` in a transaction to `ibc-0`

    ```shell
    hermes tx raw ft-transfer --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-chan channel-0 --amout 9999 --timeout-height-offset 1000 --number-msgs 1 --denom samoleans
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
    hermes tx raw packet-recv --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-chan channel-0
    ```

- query pending acks on `ibc-0`

    ```shell
    hermes query packet pending-acks --chain ibc-0 --port transfer --channel channel-0
    ```

- send acknowledgement to `ibc-0`

    ```shell
    hermes tx raw packet-ack --dst-chain ibc-0 --src-chain ibc-1 --src-port transfer --src-chan channel-1
    ```

Send those samoleans back, from `ibc-1` to `ibc-0`.

```shell
hermes tx raw ft-transfer --dst-chain ibc-0 --src-chain ibc-1 --src-port transfer --src-chan channel-1 --amount 9999 --timeout-height-offset 1000 --number-msgs 1 --denom ibc/49D321B40FCF56B0370E5673CF090389C8E9CD185209FBE1BEE5D94E58E69BDC
hermes tx raw packet-recv --dst-chain ibc-0 --src-chain ibc-1 --src-port transfer --src-chan channel-1
hermes tx raw packet-ack --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-chan channel-0
```

The `ibc/49D321B40FCF56B0370E5673CF090389C8E9CD185209FBE1BEE5D94E58E69BDC` denominator above can be obtained by querying the balance at `ibc-1` after the transfer from `ibc-0` to `ibc-1` is concluded.

Next we will test the packet timeouts.
- send 1 packet with low timeout height offset to ibc-0

    ```shell
    hermes tx raw ft-transfer --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-chan channel-0 --amount 9999 --timeout-height-offset 2 --number-msgs 1
    ```

- send timeout to `ibc-0`

    ```shell
    hermes tx raw packet-recv --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-chan channel-0
    ```

- send 1 packet with 2 second timeout to ibc-0

    ```shell
    hermes tx raw ft-transfer --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-chan channel-0 --amount 9999 --timeout-seconds 2 --number-msgs 1
    ```

- send timeout to `ibc-0`

    ```shell
    hermes tx raw packet-recv --dst-chain ibc-1 --src-chain ibc-0 --src-port transfer --src-chan channel-0
    ```

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
    hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 -o 1000 -n 1 -d samoleans
    ```

- query packet commitments on `ibc-0`

    ```shell
    hermes query packet commitments ibc-0 transfer channel-0
    ```

- query unreceived packets on `ibc-1`

    ```shell
    hermes query packet unreceived-packets ibc-1 transfer channel-1
    ```

- send `recv_packet` to `ibc-1`

    ```shell
    hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    ```

- query unreceived acks on `ibc-0`

    ```shell
    hermes query packet unreceived-acks ibc-0 transfer channel-0
    ```

- send acknowledgement to `ibc-0`

    ```shell
    hermes tx raw packet-ack ibc-0 ibc-1 transfer channel-1
    ```

Send those samoleans back, from `ibc-1` to `ibc-0`.

```shell
hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 9999 -o 1000 -n 1 -d ibc/49D321B40FCF56B0370E5673CF090389C8E9CD185209FBE1BEE5D94E58E69BDC
hermes tx raw packet-recv ibc-0 ibc-1 transfer channel-1
hermes tx raw packet-ack  ibc-1 ibc-0 transfer channel-0
```

The `ibc/49D321B40FCF56B0370E5673CF090389C8E9CD185209FBE1BEE5D94E58E69BDC` denominator above can be obtained by querying the balance at `ibc-1` after the transfer from `ibc-0` to `ibc-1` is concluded.

Next we will test the packet timeouts.
- send 1 packet with low timeout height offset to ibc-0

    ```shell
    hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 -o 2 -n 1
    ```

- send timeout to `ibc-0`

    ```shell
    hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    ```

- send 1 packet with 2 second timeout to ibc-0

    ```shell
    hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 -t 2 -n 1
    ```

- send timeout to `ibc-0`

    ```shell
    hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    ```
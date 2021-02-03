# 4. Relay Packets

### 4.1 Query balances:

- balance at ibc-0

    ```shell script
    gaiad --node tcp://localhost:26657 query bank balances $(gaiad --home data/ibc-0 keys --keyring-backend="test" show user -a)
    ```

- balance at ibc-1

    ```shell script
    gaiad --node tcp://localhost:26557 query bank balances $(gaiad --home data/ibc-1 keys --keyring-backend="test" show user -a)
    ```

Note that the addresses used in the two commands above are configured in `dev-env`.

### 4.2 Packet relaying:

First, we'll send 9999 samoleans from `ibc-0` to `ibc-1`.

- start the transfer of 9999 samoleans from `ibc-0` to `ibc-1`. This results in a Tx to `ibc-0` for a `MsgTransfer` packet

    ```shell script
    hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 1000 -n 1 -d samoleans
    ```

- query packet commitments on ibc-0

    ```shell script
    hermes query packet commitments ibc-0 transfer channel-0
    ```

- query unreceived packets on ibc-1

    ```shell script
    hermes query packet unreceived-packets ibc-1 ibc-0 transfer channel-0
    ```

- send recv_packet to ibc-1

    ```shell script
    hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    ```

- query unreceived acks on ibc-0

    ```shell script
    hermes query packet unreceived-acks ibc-0 ibc-1 transfer channel-1
    ```

- send acknowledgement to ibc-0

    ```shell script
    hermes tx raw packet-ack  ibc-0 ibc-1 transfer channel-1
    ```

- send 1 packet with low timeout height offset to ibc-0

    ```shell script
    hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 2 -n 1
    ```

- send timeout to ibc-0

    ```shell script
    hermes tx raw packet-recv ibc-1 ibc-0 transfer channel-0
    ```

Send those samoleans back, from `ibc-1` to `ibc-1`.

```shell script
hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-0 9999 1000 -n 1 -d ibc/C1840BD16FCFA8F421DAA0DAAB08B9C323FC7685D0D7951DC37B3F9ECB08A199
hermes tx raw packet-recv ibc-0 ibc-1 transfer channel-1
hermes tx raw packet-ack  ibc-1 ibc-0 transfer channel-0
```

The `ibc/C1840BD16FCFA8F421DAA0DAAB08B9C323FC7685D0D7951DC37B3F9ECB08A199` denominator above can be obtained by querying the balance at `ibc-1` after the transfer from `ibc-0` to `ibc-1` is concluded.

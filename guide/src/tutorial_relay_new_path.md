## Packet relaying on new path

Hermes packet relaying can be done over a newly established path. It performs client creation, connection and channel handshake if a relay path is present in the configuration file.

1. Specify the path between the `transfer` ports on `ibc-0` and `ibc-1` by including the following in the configuration file:

    ```toml
    [[connections]]
    a_chain = 'ibc-1'
    b_chain = 'ibc-0'

    [[connections.paths]]
    a_port = 'transfer'
    b_port = 'transfer'
    ```

2. From one terminal start hermes over this path:

   ```shell script
   hermes start ibc-0 ibc-1
   ```

    > The different modes of operations are currently under heavy development. In this release the fist path specified between two chains is selected.

    Once the path is established the relayer waits listening for IBC packet events.

3. in a separate terminal, use the transfer command to send 2 packets to `ibc0` chain:

    ```shell script
    hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 1000 -n 2
    ```
4. use the CLI to send 2 packets to `ibc1` chain:

    ```shell script
    hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-1 9999 1000 -n 2
    ```

5. Observe the output on the relayer terminal, verify that the send events are processed, and the `recv_packet` -s are sent out.

6. Query the unreceived packets on `ibc0` and `ibc1` from a different terminal

    ```shell script
    hermes query packet unreceived-packets ibc-1 ibc-0  transfer channel-0
    hermes query packet unreceived-acks ibc-0 ibc-1 transfer channel-1
    hermes query packet unreceived-packets ibc-0 ibc-1  transfer channel-1
    hermes query packet unreceived-acks ibc-1 ibc-0 transfer channel-0
    ```

    There should be no unreceived packets and acks:

    ```json
    {
      "status": "success",
      "result": []
    }
    ```

    > It may also show packets that have been sent before the relayer loop was started (Hermes currently does not flush those).

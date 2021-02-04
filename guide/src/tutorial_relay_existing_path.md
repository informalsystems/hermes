# Packet relaying on existing path

Hermes can listen to IBC packet events over a specified path and relay receive packets, acknowledgments and timeouts.

1. From one terminal start hermes using the `start` command and specify the port and a previously established channel:

   ```shell script
   hermes start ibc-0 ibc-1 transfer channel-0
   ```

    > __Note__: In this example, the channel identifier on `ibc-0`is `channel-0` while the identifier on`ibc-1` is `channel-1`

2. In a separate terminal, use the transfer command to send 2 packets to `ibc0` chain:

    ```shell script
    hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 1000 -n 2
    ```

3. Use the CLI to send 2 packets to `ibc1` chain:

    ```shell script
    hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-1 9999 1000 -n 2
    ```

4. Observe the output on the relayer terminal, verify that the send events are processed, and the `recv_packet` -s are sent out.

5. Query the unreceived packets on `ibc0` and `ibc1` from a different terminal

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

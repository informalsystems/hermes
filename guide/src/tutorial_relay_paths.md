
[WIP]
## Relaying packets using the event listening mode

In this mode the relayer listens to IBC packet events and forwards packet transactions. The relayer can start this over a new or existing channel.

### With client, connection and channel setup
The relayer can perform client creation, connection and channel handshake by configuring a relay path in the configuration  file. For example, you can specify that a channel between the `transfer` ports on `ibc-0` and `ibc-1` should be created by including the following in the configuration file:

```toml
[[connections]]
a_chain = "ibc1"
b_chain = "ibc0"

[[connections.paths]]
a_port = 'transfer'
b_port = 'transfer'
```

Then start the relayer over this path:

   ```shell script
    hermes start ibc-0 ibc-1
   ```

The relayer creates the clients, and perform the handshake for a new connection and channel between the two chains on `transfer` port. Once finished, it listens for IBC packet events and relays receive packets, acknowledgments and timeouts.

### With existing channel
The relayer can be started by specifying an existing channel


   ```shell script
    hermes start ibc-0 ibc-1 transfer channel-0
   ```

The relayer listens for IBC packet events over the specified channel and relays receive packets, acknowledgments and timeouts.

### Packet relaying
- in a separate terminal, use the packet send command to send 2 packets to `ibc0` chain:

    ```shell script
    hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-0 9999 1000 -n 2
    ```
- use the CLI to send 2 packets to `ibc1` chain:

    ```shell script
    hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-1 9999 1000 -n 2
    ```

- observe the output on the relayer terminal, verify that the send events are processed, and the `recv_packet` -s are sent out.

- query the unreceived packets on `ibc0` and `ibc1` from a different terminal

    ```shell script
    hermes query packet unreceived-packets ibc-1 ibc-0  transfer channel-0
    hermes query packet unreceived-acks ibc-0 ibc-1 transfer channel-0
    hermes query packet unreceived-packets ibc-0 ibc-1  transfer channel-0
    hermes query packet unreceived-acks ibc-1 ibc-0 transfer channel-0
    ```
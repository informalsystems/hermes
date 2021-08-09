#  Relaying
This section describes the types of relaying that hermes can perform.

Hermes can send transactions triggered by IBC events. It currently handles channel handshake and packet events:
 - [packets messages only](./packets.md#packet-relaying)
 - [channel and packet messages](./handshakes.md)

## The `start` Command

The `start` command can be used to start hermes in IBC event listen mode.

```shell
USAGE:
    hermes start <OPTIONS>

DESCRIPTION:
    Start the relayer in multi-chain mode. Relays packets and channel handshake messages between all chains in the config.
```

As described in next sub-sections, the type of relaying can be configured in the `global` section of the configuration file, by specifying different values in `strategy` field.

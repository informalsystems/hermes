# Queries

Hermes supports querying for different objects that exist on a configured chain.

The `query` command provides the following sub-commands:

| CLI name               | Description                                                                    |
| ---------------------- | ------------------------------------------------------------------------------ |
| `client`               | [Query information about clients](./client.md)                         |
| `clients`              | [Query all clients](./client.md)                                       |
| `connection`           | [Query information about connections](./connection.md)                 |
| `connections`          | [Query the identifiers of all connections on a chain](./connection.md) |
| `channel`              | [Query information about channels](./channel.md)                       |
| `channels`             | [Query the identifiers of all channels on a given chain](./channel.md) |
| `packet`               | [Query information about packets](./packet.md)                         |
| `transfer`             | [Query information about token transfers](./transfer.md)               |
| `tx`                   | [Query information about transactions](./tx.md)                        |

## Usage

```
USAGE:
    hermes query <SUBCOMMAND>

DESCRIPTION:
    Query objects from the chain

SUBCOMMANDS:
    client         Query information about clients
    clients        Query clients
    connection     Query information about connections
    connections    Query the identifiers of all connections on a chain
    channel        Query information about channels
    channels       Query the identifiers of all channels on a given chain
    packet         Query information about packets
    transfer       Query information about token transfers
    tx             Query information about transactions
```

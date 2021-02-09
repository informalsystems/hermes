# Queries

Hermes supports querying for different objects that exist on a configured chain.

The `query` command provides the following sub-commands:

| CLI name               | Description                                                                    |
| ---------------------- | ------------------------------------------------------------------------------ |
| `client`               | [Query information about clients](./query_client.html)                         |
| `clients`              | [Query all clients](./query_client.html)                                       |
| `connection`           | [Query information about connections](./query_connection.html)                 |
| `connections`          | [Query the identifiers of all connections on a chain](./query_connection.html) |
| `channel`              | [Query information about channels](./query_channel.html)                       |
| `channels`             | [Query the identifiers of all channels on a given chain](./query_channel.html) |
| `packet`               | [Query information about packets](./query_packet.html)                         |

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
```

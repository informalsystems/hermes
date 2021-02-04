# Queries

Hermes supports querying for different objects that exist on a configured chain.

The `query` command provides the following sub-commands:

| CLI name               | Description                                                                    |
| ---------------------- | ------------------------------------------------------------------------------ |
| `client`               | [query information about client(s)](./query_client.html)                       |
| `clients`              | [query all clients](./query_client.html)                                       |
| `connection`           | [query information about connection(s)](./query_connection.html)               |
| `connections`          | [query the identifiers of all connections on a chain](./query_connection.html) |
| `channel`              | [query information about channel(s)](./query_channel.html)                     |
| `channels`             | [query the identifiers of all channels on a given chain](./query_channel.html) |
| `packet`               | [query information about packet(s)](./query_packet.html)                       |

## Usage

```
USAGE:
    hermes query <SUBCOMMAND>

DESCRIPTION:
    query state from chain

SUBCOMMANDS:
    client     query information about client(s)
    clients    query clients
    connection query information about connection(s)
    connections query the identifiers of all connections on a chain
    channel    query information about channel(s)
    channels   query the identifiers of all channels on a given chain
    packet     query information about packet(s)
```

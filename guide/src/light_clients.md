# Light Clients

Using the `light` command you can add and remove light client peer information to the chain configuration.

#### Show usage

To see the available sub-commands for the `light` command run:

```shell
hermes help light
```

There are two sub-commands supported `add` and `rm`:

```shell
USAGE:
    hermes light <SUBCOMMAND>

DESCRIPTION:
    Basic functionality for managing the lite clients

SUBCOMMANDS:
    add        add a light client peer for a given chain
    rm         remove a light client peer for a given chain

```

### Adding Light Client Peers

In order to add the light client peers use the `add` command:

```shell
USAGE:
    hermes light add <OPTIONS>

DESCRIPTION:
    Add a light client peer for a given chain

POSITIONAL ARGUMENTS:
    address                   RPC network address (required)

FLAGS:
    -c, --chain-id CHAIN-ID   identifier of the chain (required)
    -s, --store STORE         path to light client store for this peer (required)
    -p, --primary             whether this is the primary peer
    -f, --force               allow overriding an existing peer
    -y, --yes                 skip confirmation
    --peer-id PEER-ID         override peer id (optional)
    --height HEIGHT           override height (optional)
    --hash HASH               override hash (optional)
```


#### Set the Primary Light Client Peer for a Chain

In order to add a light client primary peer for a given chain execute the following command:

```shell
hermes -c [CONFIG_FILE] light add tcp://[RPC_NETWORK_ADDRESS] -c [CHAIN_ID] -s [CHAIN_STORE] -p -y -f
```

#### Set the Secondary Light Client Peer for a Chain

In order to add a light client secondary peer for a given chain execute the following command:

```shell
hermes -c [CONFIG_FILE] light add tcp://[RPC_NETWORK_ADDRESS] -c [CHAIN_ID] -s [CHAIN_STORE] --peer-id 17D46D8C1576A79203A6733F63B2C9B7235DD559 -y
```

> The `peer-id` above can be any valid value for a peer id. Currently, the relayer does not validate if this secondary peer exists.

### Removing Light Client Peers

In order to remove a light client peer use the `rm` command:

```shell
USAGE:
    hermes light rm <OPTIONS>

DESCRIPTION:
    Remove a light client peer for a given chain

POSITIONAL ARGUMENTS:
    peer_id                   identifiers of peers to remove

FLAGS:
    -c, --chain-id CHAIN-ID   identifier of the chain to remove peers from
    -f, --force               force removal of primary peer
    --all                     remove all peers, implies --force
    -y, --yes                 skip confirmation

```

#### Removing all light client peers from a chain

In order to remove all light peers for a chain from the configuration execute the following command:

```shell
hermes -c [CONFIG_FILE] light rm -c [CHAIN_ID] -y --all
```

# Light Clients

Using the `light` command you can add and remove light client peers information to the chain configuration.

#### Show usage

To see the available subcommands for the `light` command run:

```shell
relayer help light
```

Currently there are two subcommands supported `add` and `rm`:

```shell
USAGE:
    relayer light <SUBCOMMAND>

DESCRIPTION:
    basic functionality for managing the lite clients

SUBCOMMANDS:
    add        add a light client peer for a given chain
    rm         remove a light client peer for a given chain

```

### Adding Light Client Peers

In order to add light client peers use the `add` command:

```shell
USAGE:
    relayer light add <OPTIONS>

DESCRIPTION:
    add a light client peer for a given chain

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

In order to add a light client peer for a given chain execute the following command:

```shell
relayer -c [CONFIG_FILE] light add tcp://[RPC_NETWORK_ADDRESS] -c [CHAIN_ID] -s [CHAIN_STORE] -p -y -f
```

#### Set the Secondary Light Client Peer for a Chain

In order to add a light client peer for a given chain execute the following command:

```shell
relayer -c [CONFIG_FILE] light add tcp://[RPC_NETWORK_ADDRESS] -c [CHAIN_ID] -s [CHAIN_STORE] --peer-id 17D46D8C1576A79203A6733F63B2C9B7235DD559 -y
```

__Note__: The `peer-id` above can be any valid value for a peer id. Currently, the relayer does not validate if this secondary peer exists.

### Removing Light Client Peers

In order to add light client peers use the `rm` command:

```shell
USAGE:
    relayer light rm <OPTIONS>

DESCRIPTION:
    remove a light client peer for a given chain

POSITIONAL ARGUMENTS:
    peer_id                   identifiers of peers to remove
                              
FLAGS:
    -c, --chain-id CHAIN-ID   identifier of the chain to remove peers from
    -f, --force               force removal of primary peer
    --all                     remove all peers, implies --force
    -y, --yes                 skip confirmation

```

#### Removing all light client peers from a chain

In order to remove all light peers configuration from a chain execute the following command:

```shell
relayer -c [CONFIG_FILE] light rm -c [CHAIN_ID] -y --all
```
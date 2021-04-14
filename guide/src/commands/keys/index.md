# Adding Keys to the Relayer

> __WARNING__: Currently the relayer does NOT support a `keyring` store to securely
> store the private key file. The key file will be stored on the local file system
> in the user __$HOME__ folder under `$HOME/.rrly`

> __BREAKING__: As of Hermes v0.2.0, the format of the keys stored on disk has changed, and
> keys which had been previously configured must now be re-imported using either the `keys add`
> or the `keys restore` commands.

---

Using the `keys` command you can add and list keys. 

#### Show usage

To see the available sub-commands for the `keys` command run:

```shell
hermes help keys
```

Currently there are two sub-commands supported `add` and `list`:

```shell
USAGE:
    hermes-cli keys <SUBCOMMAND>

DESCRIPTION:
    Manage keys in the relayer for each chain

SUBCOMMANDS:
    help       Get usage information
    add        adds a key to a configured chain
    list       list keys configured on a chain
```

### Key Seed file (Private Key)

In order to execute the command below you need a private key file (JSON). The relayer uses the private key file to sign the transactions submitted to the chain.

The private key file can be obtained by using the `keys add` on a Cosmos chain, for example for a `gaia` chain the command is:

```shell
gaiad keys add ...
```

The command outputs a JSON similar to the one below. You can save this file (e.g. `key_seed.json`) and use it to add to the relayer

```json
{
  "name": "user",
  "type": "local",
  "address": "cosmos1tc3vcuxyyac0dmayf887t95tdg7qpyql48w7gj",
  "pubkey": "cosmospub1addwnpepqgg7ng4ycm60pdxfzdfh4hjvkwcr3da59mr8k883vsstx60ruv7kur4525u",
  "mnemonic": "[24 words mnemonic]"
}
```

### Adding Keys

#### Add a private key to a chain from a key file

```shell
USAGE:
    hermes keys add <OPTIONS>

DESCRIPTION:
    Adds a key to a configured chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain

FLAGS:
    -f, --file FILE           the path to the key file (conflicts with --mnemonic)
```

To add a private key file to a chain:

```shell
hermes -c config keys add [CHAIN_ID] -f [PRIVATE_KEY_FILE]
```

If the command is successful a message similar to the one below will be displayed:

```json
Success: Added key testkey ([ADDRESS]) on [CHAIN ID] chain
```

#### Restore a private key to a chain from a mnemonic

```shell
USAGE:
    hermes keys restore <OPTIONS>

DESCRIPTION:
    restore a key to a configured chain using a mnemonic

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain

FLAGS:
    -n, --name NAME           key name
    -m, --mnemonic MNEMONIC   mnemonic to restore the key from
```

To restore a key from its mnemonic:

```shell
hermes -c config keys restore [CHAIN_ID] -m "[MNEMONIC]"
```

If the command is successful a message similar to the one below will be displayed:

```json
Success: Restore key testkey ([ADDRESS]) on [CHAIN ID] chain
```

### List keys

In order to list the private keys added to chains use the `keys list` command

```shell
USAGE:
    hermes keys list <OPTIONS>

DESCRIPTION:
    List keys configured on a chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain
```

#### Listing the private key that was added to a chain

To list the private key file that was added to a chain:

```shell
hermes -c config keys list [CHAIN_ID]
```

If the command is successful a message similar to the one below will be displayed:

```json
[CHAIN_ID] -> [KEY_NAME] ([ADDRESS])
```

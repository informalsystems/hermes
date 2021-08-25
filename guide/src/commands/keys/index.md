# Adding Keys to the Relayer

> __WARNING__: Currently the relayer does NOT support a `keyring` store to securely
> store the private key file. The key file will be stored on the local file system
> in the user __$HOME__ folder under `$HOME/.hermes/keys/`

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
    hermes keys <SUBCOMMAND>

DESCRIPTION:
    Manage keys in the relayer for each chain

SUBCOMMANDS:
    help       Get usage information
    add        Adds a key to a configured chain
    delete     Delete key(s) from a configured chain
    list       List keys configured on a chain
    restore    restore a key to a configured chain using a mnemonic
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
    hermes keys add <OPTIONS>

DESCRIPTION:
    Adds a key to a configured chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain

FLAGS:
    -f, --file FILE           path to the key file
    -n, --name NAME           name of the key (defaults to the `key_name` defined in the config)
    -p, --hd-path HD-PATH     derivation path for this key (default: m/44'/118'/0'/0/0)
```

To add a private key file to a chain:

```shell
hermes -c config.toml keys add [CHAIN_ID] -f [PRIVATE_KEY_FILE]
```

If the command is successful a message similar to the one below will be displayed:

```json
Success: Added key testkey ([ADDRESS]) on [CHAIN ID] chain
```

> **Key name:**
> By default, the key will be named after the `key_name` property specified in the configuration file.
> To use a different key name, specify the `--name` option when invoking `keys add`.
>
> ```
> hermes -c config.toml keys add [CHAINID] -f [PRIVATE_KEY_FILE] -n [KEY_NAME]
> ```

#### Restore a private key to a chain from a mnemonic

```shell
USAGE:
    hermes keys restore <OPTIONS>

DESCRIPTION:
    restore a key to a configured chain using a mnemonic

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain

FLAGS:
    -m, --mnemonic MNEMONIC   mnemonic to restore the key from
    -n, --name NAME           name of the key (defaults to the `key_name` defined in the config)
    -p, --hd-path HD-PATH     derivation path for this key (default: m/44'/118'/0'/0/0)
```

To restore a key from its mnemonic:

```shell
hermes -c config.toml keys restore [CHAIN_ID] -m "[MNEMONIC]"
```

If the command is successful a message similar to the one below will be displayed:

```json
Success: Restore key testkey ([ADDRESS]) on [CHAIN ID] chain
```

> **Key name:**
> By default, the key will be named after the `key_name` property specified in the configuration file.
> To use a different key name, specify the `--name` option when invoking `keys restore`.
>
> ```
> hermes -c config.toml keys restore [CHAINID] -m "[MNEMONIC]" -n [KEY_NAME]
> ```

### Delete keys

In order to delete the private keys added to chains use the `keys delete` command

```shell
USAGE:
    hermes keys delete <OPTIONS>

DESCRIPTION:
    Delete key(s) from a configured chain

POSITIONAL ARGUMENTS:
    chain_id                  identifier of the chain

FLAGS:
    -n, --name NAME           name of the key
    -a, --all                 delete all keys
```

#### Delete private keys that was previously added to a chain

To delete a single private key by name:

```shell
hermes -c config.toml keys delete [CHAIN_ID] -n [KEY_NAME]
```

Alternatively, to delete all private keys added to a chain:

```shell
hermes -c config.toml keys delete [CHAIN_ID] -a
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
hermes -c config.toml keys list [CHAIN_ID]
```

If the command is successful a message similar to the one below will be displayed:

```
Success:
- user2 (cosmos1attn9fxrcvjz483w3tu4cfz77ldmlyujly3q3k)
- testkey (cosmos1dw88vdekeeuta5u50p6n5lt5v5c6y2we0pu8nz)
```

**JSON:**

```shell
hermes --json -c config.toml keys list [CHAIN_ID] | jq
```

If the command is successful a message similar to the one below will be displayed:

```json
{
  "result": {
    "testkey": {
      "account": "cosmos1dw88vdekeeuta5u50p6n5lt5v5c6y2we0pu8nz",
      "address": [ 107, 142, 118, 55, 54, 206, 120, 190, 211, 148, 120, 117, 58, 125, 116, 101, 49, 162, 41, 217 ],
      "coin_type": 118,
      "private_key": "(snip)",
      "public_key": "xpub6Gc7ZUt2q1BiQYjhUextPv5bZLwosHigZYqEquPD6FkAGmHDrLiBgE5Xnh8XGZp79rAXtZn1Dt3DNQHxxgCgVQqfRMfVsRiXn6mwULBnYq7"
    },
    "user2": {
      "account": "cosmos1attn9fxrcvjz483w3tu4cfz77ldmlyujly3q3k",
      "address": [ 234, 215, 50, 164, 195, 195, 36, 42, 158, 46, 138, 249, 92, 36, 94, 247, 219, 191, 147, 146 ],
      "coin_type": 118,
      "private_key": "(snip)",
      "public_key": "xpub6FmDbeGTWVjSvHrqHfrpnMTZxpPX1V7XFiq5nMuvgwX9jumt1yUuwNAUQo8Nn36unbFShg6iSjkfMBgeY49wik7rF91N2SHvarpX62ByWMf"
    }
  },
  "status": "success"
}
```

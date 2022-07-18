# Adding Keys to the Relayer

> __WARNING__: Currently the relayer does NOT support a `keyring` store to securely
> store the private key file. The key file will be stored on the local file system
> in the user __$HOME__ folder under `$HOME/.hermes/keys/`

> __BREAKING__: As of Hermes v1.0.0, the sub-command `keys restore` has been removed.
> Please use the sub-command `keys add` in order to restore a key.

---

Using the `keys` command you can add and list keys. 

#### Show usage

To see the available sub-commands for the `keys` command run:

```shell
hermes help keys
```

The available sub-commands are the following:

```shell
USAGE:
    hermes keys <SUBCOMMAND>

DESCRIPTION:
    Manage keys in the relayer for each chain

SUBCOMMANDS:
    help       Get usage information
    add        Adds key to a configured chain or restores a key to a configured chain
                    using a mnemonic
    balance    Query balance for a key from a configured chain. If no key is given, the
                    key is retrieved from the configuration file
    delete     Delete key(s) from a configured chain
    list       List keys configured on a chain
```

### Key Seed file (Private Key)

In order to execute the command below you need a private key file (JSON). The relayer uses the private key file to sign the transactions submitted to the chain.

The private key file can be obtained by using the `keys add` on a Cosmos chain. For example, the command for `gaiad` is:

```shell
# The `key_name` parameter is the name of the key that will be found in the json output
# For example, in the "Two Local Chains" tutorial, we use "testkey".
gaiad keys add <key_name> --output json
```

The command outputs a JSON similar to the one below. 

```json
{
  "name": "testkey",
  "type": "local",
  "address": "cosmos1tc3vcuxyyac0dmayf887t95tdg7qpyql48w7gj",
  "pubkey": "cosmospub1addwnpepqgg7ng4ycm60pdxfzdfh4hjvkwcr3da59mr8k883vsstx60ruv7kur4525u",
  "mnemonic": "[24 words mnemonic]"
}
```

You can save this to a file (e.g. `key_seed.json`) and use it to add to the relayer with `hermes keys add --chain <chain_id> --key-file key_seed.json`. See the `Adding Keys` section for more details.

### Adding and restoring Keys

The command `keys add` has two exclusive flags, `--key-file` and `--mnemonic-file` which are respectively used to add and restore a key.  
If a key with the same `key_name` already exists, the flag `--overwrite` must be passed in order to overwrite the existing key or else the command will abort.

```shell
    hermes keys add [OPTIONS] --chain <CHAIN_ID> --key-file <KEY_FILE>

    hermes keys add [OPTIONS] --chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE>

DESCRIPTION:
    Adds key to a configured chain or restores a key to a configured chain using a mnemonic

OPTIONS:
        --hd-path <HD_PATH>      Derivation path for this key [default: m/44'/118'/0'/0/0]
        --key-name <KEY_NAME>    Name of the key (defaults to the `key_name` defined in the config)
        --overwrite              Overwrite the key if there is already one with the same key name

FLAGS:
        --chain <CHAIN_ID>                 Identifier of the chain
        --key-file <KEY_FILE>              Path to the key file
        --mnemonic-file <MNEMONIC_FILE>    Path to file containing mnemonic to restore the key from
```

#### Add a private key to a chain from a key file

```shell
    hermes keys add [OPTIONS] --chain <CHAIN_ID> --key-file <KEY_FILE>

DESCRIPTION:
    Adds key to a configured chain or restores a key to a configured chain using a mnemonic

OPTIONS:
        --hd-path <HD_PATH>      Derivation path for this key [default: m/44'/118'/0'/0/0]
        --key-name <KEY_NAME>    Name of the key (defaults to the `key_name` defined in the config)
        --overwrite              Overwrite the key if there is already one with the same key name

FLAGS:
        --chain <CHAIN_ID>                 Identifier of the chain
        --key-file <KEY_FILE>              Path to the key file
```

To add a private key file to a chain:

```shell
hermes --config config.toml keys add --chain [CHAIN_ID] --key-file [PRIVATE_KEY_FILE]
```

The content of the file key should have the same format as the output of the `gaiad keys add` command:

```json
{
  "name": "testkey",
  "type": "local",
  "address": "cosmos1tc3vcuxyyac0dmayf887t95tdg7qpyql48w7gj",
  "pubkey": "cosmospub1addwnpepqgg7ng4ycm60pdxfzdfh4hjvkwcr3da59mr8k883vsstx60ruv7kur4525u",
  "mnemonic": "[24 words mnemonic]"
}
```

If the command is successful a message similar to the one below will be displayed:

```json
Success: Added key testkey ([ADDRESS]) on [CHAIN ID] chain
```

> **Key name:**
> By default, the key will be named after the `key_name` property specified in the configuration file.
> To use a different key name, specify the `--key-name` option when invoking `keys add`.
>
> ```
> hermes --config config.toml keys add --chain [CHAINID] --key-file [PRIVATE_KEY_FILE] --key-name [KEY_NAME]
> ```

#### Restore a private key to a chain from a mnemonic

```shell
    hermes keys add [OPTIONS] --chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE>

DESCRIPTION:
    Adds key to a configured chain or restores a key to a configured chain using a mnemonic

OPTIONS:
        --hd-path <HD_PATH>      Derivation path for this key [default: m/44'/118'/0'/0/0]
        --key-name <KEY_NAME>    Name of the key (defaults to the `key_name` defined in the config)
        --overwrite              Overwrite the key if there is already one with the same key name

FLAGS:
        --chain <CHAIN_ID>                 Identifier of the chain
        --mnemonic-file <MNEMONIC_FILE>    Path to file containing mnemonic to restore the key from
```

To restore a key from its mnemonic:

```shell
hermes --config config.toml keys add --chain [CHAIN_ID] --mnemonic-file "[MNEMONIC_FILE]"
```

or using an explicit [derivation path](https://github.com/satoshilabs/slips/blob/master/slip-0044.md), for example
an Ethereum coin type (used for Evmos, Injective, Umee, Cronos, and
possibly other networks):

```shell
hermes --config config.toml keys add --chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE> --hd-path "m/44'/60'/0'/0/0"
```

The mnemonic file needs to have the 24 mnemonic words on the same line, separated by a white space. So the content should have the following format:
```
word1 word2 word3 ... word24
```

If the command is successful a message similar to the one below will be displayed:

```json
Success: Restore key testkey ([ADDRESS]) on [CHAIN ID] chain
```

> **Key name:**
> By default, the key will be named after the `key_name` property specified in the configuration file.
> To use a different key name, specify the `--key-name` option when invoking `keys add`.
>
> ```
> hermes --config config.toml keys add --chain [CHAINID] --mnemonic-file "[MNEMONIC_FILE]" --key-name [KEY_NAME]
> ```

### Delete keys

In order to delete the private keys added to chains use the `keys delete` command

```shell
USAGE:
    hermes keys delete [OPTIONS] --chain <CHAIN_ID>

DESCRIPTION:
    hermes keys delete --chain <CHAIN_ID> --key-name <KEY_NAME>

    hermes keys delete --chain <CHAIN_ID> --all

FLAGS:
        --all                    Delete all keys
        --chain <CHAIN_ID>       Identifier of the chain
        --key-name <KEY_NAME>    Name of the key
```

#### Delete private keys that was previously added to a chain

To delete a single private key by name:

```shell
hermes --config config.toml keys delete --chain [CHAIN_ID] --key-name [KEY_NAME]
```

Alternatively, to delete all private keys added to a chain:

```shell
hermes --config config.toml keys delete --chain [CHAIN_ID] --all
```

### List keys

In order to list the private keys added to chains use the `keys list` command

```shell
USAGE:
    hermes keys list --chain <CHAIN_ID>

DESCRIPTION:
    List keys configured on a chain

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain
```

#### Listing the private key that was added to a chain

To list the private key file that was added to a chain:

```shell
hermes --config config.toml keys list --chain [CHAIN_ID]
```

If the command is successful a message similar to the one below will be displayed:

```
Success:
- user2 (cosmos1attn9fxrcvjz483w3tu4cfz77ldmlyujly3q3k)
- testkey (cosmos1dw88vdekeeuta5u50p6n5lt5v5c6y2we0pu8nz)
```

**JSON:**

```shell
hermes --json --config config.toml keys list --chain [CHAIN_ID] | jq
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
### Query balance

In order to retrieve the balance of an account associated with a key use the `keys balance` command

```shell
USAGE:
    hermes keys balance [OPTIONS] --chain <CHAIN_ID>

DESCRIPTION:
    Query balance for a key from a configured chain. If no key is given, the key is retrieved from the configuration file

OPTIONS:
        --key-name <KEY_NAME>    (optional) name of the key (defaults to the `key_name` defined in
                                 the config)

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain
```

If the command is successful a message with the following format will be displayed:

```
Success: balance for key `KEY_NAME`: 100000000000 stake
```

**JSON:**

```shell
hermes --json keys balance [OPTIONS] --chain <CHAIN_ID>
```

If the command is successful a message with the following format will be displayed:

```json
{
  "result": {
    "amount": "99989207",
    "denom": "stake"
  },
  "status": "success"
}
```

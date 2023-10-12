# Adding Keys to Hermes

> __WARNING__: Currently Hermes does NOT support a `keyring` store to securely
> store the private key file. The key file will be stored on the local file system
> in the folder set by the configuration `key_store_folder` which defaults
> to `key_store_folder = '$HOME/.hermes/keys'`.

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
{{#include ../../../templates/help_templates/keys.md}}
```

### Key Seed file (Private Key)

In order to execute the command below you need a private key file (JSON). Hermes uses the private key file to sign the transactions submitted to the chain.

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

You can save this to a file (e.g. `key_seed.json`) and use it to add to Hermes with `{{#template ../../../templates/commands/hermes/keys/add_2.md CHAIN_ID=<CHAIN_ID> KEY_FILE=key_seed.json}}`. See the `Adding Keys` section for more details.

### Adding and restoring Keys

The command `keys add` has two exclusive flags, `--key-file` and `--mnemonic-file` which are respectively used to add and restore a key.  
If a key with the same `key_name` already exists, the flag `--overwrite` must be passed in order to overwrite the existing key or else the command will abort.

```shell
{{#include ../../../templates/help_templates/keys/add.md}}
```

#### Add a private key to a chain from a key file

```shell
{{#template ../../../templates/commands/hermes/keys/add_2.md CHAIN_ID=<CHAIN_ID> KEY_FILE=<PRIVATE_KEY_FILE>}}
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
Success: Added key testkey (<ADDRESS>) on <CHAIN_ID> chain
```

> **Key name:**
> By default, the key will be named after the `key_name` property specified in the configuration file.
> To use a different key name, specify the `--key-name` option when invoking `keys add`.
>
> ```
> {{#template ../../../templates/commands/hermes/keys/add_2.md CHAIN_ID=<CHAIN_ID> KEY_FILE=<PRIVATE_KEY_FILE> OPTIONS= --key-name [KEY_NAME]}}
> ```

#### Restore a private key to a chain from a mnemonic

```shell
{{#template ../../../templates/commands/hermes/keys/add_4.md CHAIN_ID=<CHAIN_ID> MNEMONIC_FILE=<MNEMONIC_FILE>}}
```

or using an explicit [derivation path](https://github.com/satoshilabs/slips/blob/master/slip-0044.md), for example
an Ethereum coin type (used for Evmos, Injective, Umee, Cronos, and
possibly other networks):

```shell
{{#template ../../../templates/commands/hermes/keys/add_4.md CHAIN_ID=<CHAIN_ID> MNEMONIC_FILE=<MNEMONIC_FILE> OPTIONS= --hd-path "m/44'/60'/0'/0/0"}}
```

The mnemonic file needs to have the 24 mnemonic words on the same line, separated by a white space. So the content should have the following format:
```
word1 word2 word3 ... word24
```

If the command is successful a message similar to the one below will be displayed:

```json
Success: Restore key testkey (<ADDRESS>) on <CHAIN_ID> chain
```

> **Key name:**
> By default, the key will be named after the `key_name` property specified in the configuration file.
> To use a different key name, specify the `--key-name` option when invoking `keys add`.
>
> ```
> {{#template ../../../templates/commands/hermes/keys/add_4.md CHAIN_ID=<CHAIN_ID> MNEMONIC_FILE=<MNEMONIC_FILE> OPTIONS= --key-name <KEY_NAME>}}
> ```

### Delete keys

In order to delete the private keys added to chains use the `keys delete` command

```shell
{{#include ../../../templates/help_templates/keys/delete.md}}
```

#### Delete private keys that was previously added to a chain

To delete a single private key by name:

```shell
{{#template ../../../templates/commands/hermes/keys/delete_1.md CHAIN_ID=<CHAIN_ID> KEY_NAME=<KEY_NAME>}}
```

Alternatively, to delete all private keys added to a chain:

```shell
hermes --config config.toml keys delete --chain <CHAIN_ID> --all
```

### List keys

In order to list the private keys added to chains use the `keys list` command

```shell
{{#include ../../../templates/help_templates/keys/list.md}}
```

#### Listing the private key that was added to a chain

To list the private key file that was added to a chain:

```shell
{{#template ../../../templates/commands/hermes/keys/list_1.md CHAIN_ID=<CHAIN_ID>}}
```

If the command is successful a message similar to the one below will be displayed:

```
Success:
- user2 (cosmos1attn9fxrcvjz483w3tu4cfz77ldmlyujly3q3k)
- testkey (cosmos1dw88vdekeeuta5u50p6n5lt5v5c6y2we0pu8nz)
```

**JSON:**

```shell
{{#template ../../../templates/commands/hermes/keys/list_1.md CHAIN_ID=<CHAIN_ID> GLOBALOPTIONS=  --json}} | jq
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
{{#include ../../../templates/help_templates/keys/balance.md}}
```

If the command is successful a message with the following format will be displayed:

```
Success: balance for key `KEY_NAME`: 100000000000 stake
```

**JSON:**

```shell
{{#template ../../../templates/commands/hermes/keys/balance_1.md CHAIN_ID=<CHAIN_ID> GLOBALOPTIONS=  --json}}
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

# Setup Hermes

In this section, you will learn how to setup Hermes to relay between the Hub and Osmosis.

## Setup accounts

First, you need a wallet with enough funds on both chains. It is difficult to estimate how much gas you will spend as it depends on many parameters like:
- The volume of IBC transfers on the channels you are relaying.
- The chain's activity. More congestion means higher gas prices.
- The transaction's size. Bigger transactions need more gas. 

### Adding a private key

You can add a private key by two different ways:

- If you have a [key-seed file](../../documentation/commands/keys/index.md#key-seed-file-private-key), use the commands :
    ```shell
    hermes keys add --chain cosmoshub-4 --key-file key_file_hub.json
    hermes keys add --chain osmosis-1 --key-file key_file_osmosis.json 
    ```
>__NOTE__: Do not confuse the `chain-name` and the `chain-id` which follows the format `chain_name-version`.

- If you have a `mnemonic`, you can restore a private key from a [mnemonic-file](../../documentation/commands/keys/index.md#restore-a-private-key-to-a-chain-from-a-mnemonic). The following steps create a `mnemonic-file` and restore its key:
    ```shell
    echo word1 ... word12or24 > mnemonic_file_hub
    hermes keys add --chain cosmoshub-4 --mnemonic-file mnemonic_file_hub.json
    rm mnemonic_file_hub
    echo word1 ... word12or24 > mnemonic_file_osmosis
    hermes keys add --chain cosmoshub-4 --mnemonic-file mnemonic_file_osmosis.json
    rm mnemonic_file_osmosis
    ``` 

## Configuration file

Then, you need to create a configuration file for Hermes. The command `hermes config auto` provides a way to automatically generate a configuration file for chains in the [chain-registry](https://github.com/cosmos/chain-registry):

```shell
hermes config auto --output $HOME/.hermes/config.toml --chains cosmoshub osmosis
```
__NOTE__: This command also generates packet filters from the [_IBC](https://github.com/cosmos/chain-registry/tree/master/_IBC) folder in the chain-registry.

__config.toml__
```

```

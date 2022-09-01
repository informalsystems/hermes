# Setup Hermes

In this section, you will learn how to set up Hermes to relay between the Hub and Osmosis. You will relay on channels that are already created. **It is strongly advised not to create any channels between two chains if another one with the same port already exists.**

---

## Setup accounts

First, you need a wallet with enough funds on both chains. This tutorial assumes that you already have wallets created on the chains you want to relay on, and that these wallets have funds allocated to each of them.

### Adding a private key

You can add a private key using one of two different ways:

- If you have a [key-seed file](../../documentation/commands/keys/index.md#key-seed-file-private-key), use the commands :
    ```shell
    {{#template ../../templates/commands/hermes/keys_add_key_file chain=cosmoshub-4 key-file=key_file_hub.json}}
    {{#template ../../templates/commands/hermes/keys_add_key_file chain=osmosis-1 key-file=key_file_osmosis.json}}
    ```
>__NOTE__: Do not confuse the `chain-name` and the `chain-id` which follows the format `chain_name-version`.

- If you have a `mnemonic`, you can restore a private key from a [mnemonic-file](../../documentation/commands/keys/index.md#restore-a-private-key-to-a-chain-from-a-mnemonic). The following steps create a `mnemonic-file` and restore its key for each chain under names `keyhub` and `keyosmosis` :
    ```shell
    echo word1 ... word12or24 > mnemonic_file_hub
    {{#template ../../templates/commands/hermes/keys_add_mnemonic chain=cosmoshub-4 mnemonic-file=mnemonic_file_hub.json key-name=keyhub}}
    rm mnemonic_file_hub
    echo word1 ... word12or24 > mnemonic_file_osmosis
    {{#template ../../templates/commands/hermes/keys_add_mnemonic chain=osmosis-1 mnemonic-file=mnemonic_file_osmosis.json key-name=keyosmosis}}
    rm mnemonic_file_osmosis
    ``` 

## Configuration file

Then, you need to create a configuration file for Hermes (more details in the [documentation](../../documentation/configuration/index.md)). 

The command `hermes config auto` provides a way to automatically generate a configuration file for chains in the [chain-registry](https://github.com/cosmos/chain-registry):

```shell
{{#template ../../templates/commands/hermes/config_auto output=$HOME/.hermes/config.toml chains=cosmoshub:keyhub osmosis:keyosmosis}}
```
>__NOTE__: This command also automatically finds IBC paths and generates packet filters from the [_IBC](https://github.com/cosmos/chain-registry/tree/master/_IBC) folder in the chain-registry.

If the command runs successfully, it should output:
```
2022-08-26T11:40:35.164371Z  INFO ThreadId(01) using default configuration from '$HOME/.hermes/config.toml'
2022-08-26T11:40:35.165353Z  INFO ThreadId(01) Fetching configuration for chains: ["cosmoshub", "osmosis"]
2022-08-26T11:40:36.253328Z  WARN ThreadId(01) cosmoshub-4: uses key "keyhub"
2022-08-26T11:40:36.253704Z  WARN ThreadId(01) osmosis-1: uses key "keyosmosis"
2022-08-26T11:40:36.253860Z  WARN ThreadId(01) Gas parameters are set to default values.
SUCCESS "Config file written successfully : $HOME/.hermes/config.toml."
```
And generate the following configuration : 

__config.toml__
```toml
{{#template ../../templates/files/hermes/production/config.toml}}
```
>__NOTE__: You might not have the same RPC and gRPC endpoints in your configuration file as they are randomly selected in the chain-registry.

The command created packet filters so the relayer will only relay on `channel-0` for `osmosis-1` and `channel-141` for `cosmoshub-4`. It uses RPC and gRPC endpoints found in the chain registry. If you also run a full node, you can replace the endpoints with your own. It has many advantages as you can accept transactions with lower gas.

>__WARNING__: It is difficult to estimate how much gas you will spend as it depends on many parameters like:
> - The volume of transactions. More congestion means higher gas prices.
> - The transaction's size. Bigger transactions need more gas. 
> - The volume of IBC messages to relay.
> 
> We cannot provide a way to precisely set those parameters. However, you can refer to [other operators' configuration](https://github.com/informalsystems/ibc-rs/discussions/2472#discussioncomment-3331695). You can also find IBC transfers on [mintscan.io](https://www.mintscan.io/cosmos/txs) to observe how much other operators are spending. But remember that if the gas wanted is too low, the transactions will fail. If the gas price is too high gas will be wasted, but the transactions will have a higher priority. 

For the tutorial, we will follow the [example of Crypto Crew](https://github.com/notional-labs/notional/blob/master/relaying/hermes/all-ibc.toml) and set the gas parameters as follows.

- For Cosmoshub:
```toml
{{#template ../../templates/files/hermes/production/default_gas_cosmoshub}}
```

- For Osmosis:
```toml
{{#template ../../templates/files/hermes/production/default_gas_osmosis}}
```

>__NOTE__: `max_msg_nums` defines the number of messages that can be sent in the same transaction. 

>__DISCLAIMER__: These parameters need to be tuned. We can not guarantee that they will always work and kept up to date.

## Health-check

Finally, perform a `health-check` to verify that your setup is correct with:
```shell
{{#template ../../templates/commands/hermes/health_check}}
``` 

If the command runs successfully, it should output:
```
2022-08-26T15:54:21.321683Z  INFO ThreadId(01) using default configuration from '$HOME/.hermes/config.toml'
2022-08-26T15:54:21.321882Z  INFO ThreadId(01) [cosmoshub-4] performing health check...
2022-08-26T15:54:22.909339Z  WARN ThreadId(01) chain is healthy chain=cosmoshub-4
2022-08-26T15:54:22.909374Z  INFO ThreadId(01) [osmosis-1] performing health check...
2022-08-26T15:54:23.954362Z  INFO ThreadId(01) chain is healthy chain=osmosis-1
SUCCESS performed health check for all chains in the config
```

>__WARNING__: In the previous tutorials, after setting up Hermes, we started by creating a new relay path. In production, the relay path most likely already exists and does not need to be created. **Do not create channels between the Hub and Osmosis.**

---

## Next steps

You are now ready to relay. In the [next chapter](./start-relaying.md), you will start relaying and monitoring Hermes with Grafana.

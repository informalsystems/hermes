# Setup Hermes

In this section, you will learn how to set up Hermes to relay between the Hub and Osmosis.

---

## Setup accounts

First, you need a wallet with enough funds on both chains. We suppose that you already know how to create a wallet on the chains you want and to transfer them some funds.

### Adding a private key

You can add a private key by two different ways:

- If you have a [key-seed file](../../documentation/commands/keys/index.md#key-seed-file-private-key), use the commands :
    ```shell
    hermes keys add --chain cosmoshub-4 --key-file key_file_hub.json
    hermes keys add --chain osmosis-1 --key-file key_file_osmosis.json 
    ```
>__NOTE__: Do not confuse the `chain-name` and the `chain-id` which follows the format `chain_name-version`.

- If you have a `mnemonic`, you can restore a private key from a [mnemonic-file](../../documentation/commands/keys/index.md#restore-a-private-key-to-a-chain-from-a-mnemonic). The following steps create a `mnemonic-file` and restore its key for each chain under names `keyhub` and `keyosmosis` :
    ```shell
    echo word1 ... word12or24 > mnemonic_file_hub
    hermes keys add --chain cosmoshub-4 --mnemonic-file mnemonic_file_hub.json --key-name keyhub
    rm mnemonic_file_hub
    echo word1 ... word12or24 > mnemonic_file_osmosis
    hermes keys add --chain cosmoshub-4 --mnemonic-file mnemonic_file_osmosis.json --key-name keyosmosis
    rm mnemonic_file_osmosis
    ``` 

## Configuration file

Then, you need to create a configuration file for Hermes (more details in the [documentation](../../documentation/config.md)). 

The command `hermes config auto` provides a way to automatically generate a configuration file for chains in the [chain-registry](https://github.com/cosmos/chain-registry):

```shell
hermes config auto --output $HOME/.hermes/config.toml --chains cosmoshub:keyhub osmosis:keyosmosis
```
__NOTE__: This command also automatically finds IBC paths and generates packet filters from the [_IBC](https://github.com/cosmos/chain-registry/tree/master/_IBC) folder in the chain-registry.

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
```
[global]
log_level = 'info'
[mode.clients]
enabled = true
refresh = true
misbehaviour = false

[mode.connections]
enabled = false

[mode.channels]
enabled = false

[mode.packets]
enabled = true
clear_interval = 100
clear_on_start = true
tx_confirmation = false

[rest]
enabled = false
host = '127.0.0.1'
port = 3000

[telemetry]
enabled = false
host = '127.0.0.1'
port = 3001

[[chains]]
id = 'cosmoshub-4'
type = 'CosmosSdk'
rpc_addr = 'https://rpc.cosmoshub.strange.love/'
websocket_addr = 'wss://rpc.cosmoshub.strange.love/websocket'
grpc_addr = 'https://grpc-cosmoshub-ia.notional.ventures/'
rpc_timeout = '10s'
account_prefix = 'cosmos'
key_name = 'keyhub'
key_store_type = 'Test'
store_prefix = 'ibc'
default_gas = 100000
max_gas = 400000
gas_multiplier = 1.1
max_msg_num = 30
max_tx_size = 2097152
clock_drift = '5s'
max_block_time = '30s'
memo_prefix = ''
sequential_batch_tx = false

[chains.trust_threshold]
numerator = '1'
denominator = '3'

[chains.gas_price]
price = 0.1
denom = 'uatom'

[chains.packet_filter]
policy = 'allow'
list = [[
    'transfer',
    'channel-141',
]]

[chains.address_type]
derivation = 'cosmos'

[[chains]]
id = 'osmosis-1'
type = 'CosmosSdk'
rpc_addr = 'https://rpc.osmosis.interbloc.org/'
websocket_addr = 'wss://rpc.osmosis.interbloc.org/websocket'
grpc_addr = 'https://grpc-osmosis-ia.notional.ventures/'
rpc_timeout = '10s'
account_prefix = 'osmo'
key_name = 'keyosmosis'
key_store_type = 'Test'
store_prefix = 'ibc'
default_gas = 100000
max_gas = 400000
gas_multiplier = 1.1
max_msg_num = 30
max_tx_size = 2097152
clock_drift = '5s'
max_block_time = '30s'
memo_prefix = ''
sequential_batch_tx = false

[chains.trust_threshold]
numerator = '1'
denominator = '3'

[chains.gas_price]
price = 0.1
denom = 'uosmo'

[chains.packet_filter]
policy = 'allow'
list = [[
    'transfer',
    'channel-0',
]]

[chains.address_type]
derivation = 'cosmos'
```

As you can observe, the command created packet filters so the relayer will only relay on `channel-0` for osmosis and `channel-141` for the Hub. It uses RPC and gRPC endpoints found in the chain-registry. If you also run a full node, you can replace the endpoints by your own. It has many advantages as you can accept transactions with lower gas.

>__WARNING__: It is difficult to estimate how much gas you will spend as it depends on many parameters like:
> - The volume of transactions. More congestion means higher gas prices.
> - The transaction's size. Bigger transactions need more gas. 
> - The volume of IBC messages to relay.
> We cannot provide a way to precisely set those parameters. However, you can refer to [other relayer's configuration](https://github.com/informalsystems/ibc-rs/discussions/2472#discussioncomment-3331695). You can also find IBC transfers on [mintscan.io](https://www.mintscan.io/cosmos/txs) to observe how much other operators are spending. But remember that if the gas wanted is too low, the transactions will fail. If the gas price is too high gas will be wasted, but the transaction will have a higher priority. 

For the tutorial, we will follow the [example of Crypto Crew](https://github.com/notional-labs/notional/blob/master/relaying/hermes/all-ibc.toml) and set the gas parameters as follows.

- For Cosmoshub:
    ```
    default_gas = 2000000
    max_gas = 10000000
    gas_multiplier = 1.1
    max_msg_num = 25
    ...
    [chains.gas_price]
    price = 0.005
    denom = 'uatom'
    ```

- For Osmosis:
    ```
    default_gas = 5000000
    max_gas = 15000000
    gas_multiplier = 1.1
    max_msg_num = 20
    ...
    [chains.gas_price]
    price = 0.0026
    denom = 'uosmo'
    ```

>__NOTE__: `max_msg_nums` defines the number of messages that can be sent in the same transaction. 

>__DISCLAIMER__: These parameters need to be tuned. We can not guarantee that they will always work.

## Health-check

Finally, perform a `health-check` to verify that your setup is correct with:
```shell
hermes health-check
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

---

## Next steps

You are now ready to relay. In the [next chapter](./start-relaying.md), you will start relaying and monitoring Hermes with Grafana.
# Configuration

In order to run Hermes, you will need to have a configuration file.

The format supported for the configuration file is [TOML](https://toml.io/en/).

By default, Hermes expects the configuration file to be located at `$HOME/.hermes/config.toml`.

This can be overridden by supplying the `-c` flag when invoking `hermes`, before the
name of the command to run, eg. `hermes -c my_config.toml query connection channels ibc-1 connection-1`.

> The current version of Hermes does not support managing the configuration file programmatically.
> You will need to use a text editor to create the file and add content to it.

```bash
hermes [-c CONFIG_FILE] COMMAND
```

## Table of contents

<!-- toc -->

## Configuration format

The configuration file must have one `global` section, and one `chains` section for each chain.

### `[global]`

The `global` section has parameters that apply globally to the relayer operation.

#### Parameters

* __strategy__: *(string)* Specify the strategy to be used by the relayer. Default: `packets`
  Two options are currently supported:
    - `all`: Relay packets and perform channel and connection handshakes.
    - `packets`: Relay packets only.

* __log_level__: *(string)* Specify the verbosity for the relayer logging output. Valid options are 'error', 'warn', 'info', 'debug', 'trace'. Default: `info`.
  For more information on parametrizing the log output, see the section [help/log-level][log-level].

Here is an example for the `global` section:

```toml
[global]
strategy = 'packets'
log_level = 'info'
```

### `[telemetry]`

The `telemetry` section defines parameters for Hermes' built-in [telemetry](telemetry.md) capabilities.

#### Parameters

* __enabled__: *(boolean)* Whether or not to enable the telemetry service. Default: `false`.

* __host__: *(string)* Specify the IPv4/6 host over which the built-in HTTP server will serve the metrics gathered by the telemetry service. Default: `127.0.0.1`

* __port__: *(u16)* Specify the port over which the built-in HTTP server will serve the metrics gathered by the telemetry service. Default: `3001`

Here is an example for the `telemetry` section:

```toml
[telemetry]
enabled = true
host = '127.0.0.1'
port = 3001
```

### `[[chains]]`

A `chains` section includes parameters related to a chain and the full node to which the relayer can send transactions and queries.

#### Parameters

* __id__: *(string)* Specify the chain ID. For example `ibc-0`

* __rpc_addr__: *(string)* Specify the RPC address and port where the chain RPC server listens on. For example `http://localhost:26657`

* __grpc_addr__: *(string)* Specify the GRPC address and port where the chain GRPC server listens on. For example `http://localhost:9090`

* __websocket_addr__: *(string)* Specify the WebSocket address and port where the chain WebSocket server listens on. For example `ws://localhost:26657/websocket`

* __rpc_timeout__: *(string)* Specify the maximum amount of time (duration) that the RPC requests should take before timing out. Default: `10s` (10 seconds).

* __account_prefix__: *(string)* Specify the prefix used by the chain. For example `cosmos`

* __key_name__: *(string)* Specify the name of the private key to use for signing transactions. See the [Adding Keys](commands/keys/index.md#adding-keys) chapter for for more information about managing signing keys.

* __store_prefix__: *(string)* Specify the store prefix used by the on-chain IBC modules. For example `ibc`.

* __max_gas__: *(u64)* Specify the maximum amount of gas to be used as the gas limit for a transaction. Default: `300000`

* __gas_price__: *(table)*
  * __price__: *(f64)* Specify the price per gas used of the fee to submit a transaction.
  * __denom__: *(string)* Specify the denomination of the fee.

* __gas_adjustment__: *(f64)* Specify by what percentage to increase the gas estimate used to compute the fee, to account for potential estimation error. Default: `0.1`, ie. 10%.

* __max_msg_num__: *(u64)* Specify how many IBC messages at most to include in a single transaction. Default: `30`

* __max_tx_size__: *(u64)* Specify the maximum size, in bytes, of each transaction that Hermes will submit. Default: `2097152` (2 MiB)

* __clock_drift__: *(string)*  Specify the maximum amount of time to tolerate a clock drift. The clock drift parameter defines how much new (untrusted) header's Time can drift into the future. Default: `5s`

* __trusting_period__: *(string)* Specify the amount of time to be used as the light client trusting period. It should be significantly less than the unbonding period (e.g. unbonding period = 3 weeks, trusting period = 2 weeks). Default: `14days` (336 hours)

* __trust_threshold__: *(table)* Specify the trust threshold for the light client, ie. the maximum fraction of validators which have changed between two blocks. Default: `{ numerator = '1', denominator = '3' }`, ie. 1/3.
  * __numerator__: *(string)* The numerator of the fraction (must parse to a `u64`).
  * __denominator__: *(string)* The denominator of the fraction (must parse to a `u64`).

For example if you want to add a configuration for a chain named `ibc-0`:

```toml
[[chains]]
id = 'ibc-0'
rpc_addr = 'http://127.0.0.1:26657'
grpc_addr = 'http://127.0.0.1:9090'
websocket_addr = 'ws://localhost:26657/websocket'
rpc_timeout = '10s'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
max_gas = 2000000
gas_price = { price = 0.001, denom = 'stake' }
gas_adjustment = 0.1
clock_drift = '5s'
trusting_period = '14days'
```

## Adding private keys

For each chain configured you need to add a private key for that chain in order to submit [transactions](./commands/raw/index.md), please refer to the [Keys](./commands/keys/index.md) sections in order to learn how to add the private keys that are used by the relayer.

## Example configuration file

Here is a full example of a configuration file with two chains configured:

```toml
[global]
strategy = 'packets'
log_level = 'info'

[[chains]]
id = 'ibc-0'
rpc_addr = 'http://127.0.0.1:26657'
grpc_addr = 'http://127.0.0.1:9090'
websocket_addr = 'ws://localhost:26657/websocket'
rpc_timeout = '10s'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
max_gas = 2000000
gas_price = { price = 0.001, denom = 'stake' }
gas_adjustment = 0.1
clock_drift = '5s'
trusting_period = '14days'
trust_threshold = { numerator = '1', denominator = '3' }

[[chains]]
id = 'ibc-1'
rpc_addr = 'http://127.0.0.1:26557'
grpc_addr = 'http://127.0.0.1:9091'
websocket_addr = 'ws://localhost:26557/websocket'
rpc_timeout = '10s'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
max_gas = 2000000
gas_price = { price = 0.001, denom = 'stake' }
gas_adjustment = 0.1
clock_drift = '5s'
trusting_period = '14days'
trust_threshold = { numerator = '1', denominator = '3' }
```

## Update the configuration without restarting Hermes

Before Hermes 0.6.0, the only way to get Hermes to pick up a change in the
configuration was to stop and restart Hermes.

As of version 0.6.0, Hermes will react to receiving a `SIGHUP` signal
by reloading the `[chains]` section of the configuration, and
stopping, starting or restarting the affected workers.

For example, say you start with the configuration given in the previous section
in `~/.hermes/config.toml, ie. with two chains `ibc-0` and `ibc-1`.

1. Start three chains `ibc-0`, `ibc-1` and `ibc-2`:

    ```shell
    ./scripts/dev-env ibc-0 ibc-1 ibc-2
    ```

2. Start Hermes

    ```shell
    hermes start
    ```

3. Add the configuration for the chain `ibc-2` to the configuration file:

    ```toml
    [[chains]]
    id = 'ibc-2'
    rpc_addr = 'http://127.0.0.1:26457'
    grpc_addr = 'http://127.0.0.1:9092'
    websocket_addr = 'ws://127.0.0.1:26457/websocket'
    rpc_timeout = '10s'
    account_prefix = 'cosmos'
    key_name = 'testkey'
    store_prefix = 'ibc'
    max_gas = 20000000
    gas_price = { price = 0.001, denom = 'stake' }
    clock_drift = '5s'
    trusting_period = '14days'
    ```

4. Change the configuration of the chain `ibc-0`, eg. the `max_gas` property.

5. Send a `SIGHUP` signal to the `hermes` process:

    > ⚠️  **Warning:** the command below will send a `SIGHUP` signal to the first
    > process in the list emitted by `ps aux` which contains the string `hermes`.
    > Alternatively, you can look up the process ID (PID) of the `hermes` process
    > you want to target and use `kill -SIGHUP PID`.

    ```shell
    ps aux | rg hermes | awk '{ print $2 }' | head -n1 | xargs -I{} kill -SIGHUP {}
    ```

6. Watch the output of Hermes, it will show that Hermes has picked up the changes in
   the config. Hermes is now relaying between the three chains and using the new
   maximum amount of gas specified for `ibc-0`.

   ```
   ...

   INFO reloading configuration (triggered by SIGHUP)
   INFO configuration successfully reloaded
   INFO updating existing chain chain.id=ibc-1
   INFO adding new chain chain.id=ibc-2
   ```

To make sure Hermes ends up in the expected state, check out the documentation
on [inspecting the relayer state](help.md#inspecting-the-relayer-state).

## Next steps

Now that you learned how to build the relayer and how to create a configuration file, you can go to the [`Two Chains`](./tutorials/local-chains/index.md) tutorial to learn how to perform some local testing connecting the relayer to two local chains.

[log-level]: ./help.html#parametrizing-the-log-output-level


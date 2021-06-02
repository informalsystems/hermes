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

## Sections

The configuration file must have one `global` section, and one `chains` section for each chain.

### `[global]`

The `global` section has parameters that apply globally to the relayer operation.

#### Parameters

* __strategy__: *(string)* Specify the strategy to be used by the relayer. Default: `all`
  Two options are currently supported:
    - `all`: Relay packets and perform channel handshakes.
    - `packets`: Relay packets only.

* __log_level__: *(string)* Specify the verbosity for the relayer logging output. Valid options are 'error', 'warn', 'info', 'debug', 'trace'. Default value is `info`.
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

* __rpc_timeout__: *(string)* Specify the maximum amount of time (duration) that the RPC requests should take before timing out. Default value is `10s` (10 seconds).

* __account_prefix__: *(string)* Specify the prefix used by the chain. For example `cosmos`

* __key_name__: *(string)* Specify the name of the private key to use for signing transactions. See the [Adding Keys](commands/keys/index.md#adding-keys) chapter for for more information about managing signing keys.

* __store_prefix__: *(string)* Specify the store prefix used by the on-chain IBC modules. For example `ibc`.

* __gas__: *(u64)* Specify the maximum amount of gas to be used as the gas limit for a transaction. Default value is `300000`

* __fee_denom__: *(string)* Specify the denom to be used in the fee for a transaction.

* __fee_amount__: *(u64)* Specify the amount value to be used in the fee for a transaction. Default value is `1000`

* __clock_drift__: *(string)*  Specify the maximum amount of time to tolerate a clock drift. The clock drift parameter defines how much new (untrusted) header's Time can drift into the future. Default value is `5s`

* __trusting_period__: *(string)* Specify the amount of time to be used as the trusting period. It should be significantly less than the unbonding period (e.g. unbonding period = 3 weeks, trusting period = 2 weeks). Default value is `14days` (336 hours)

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
gas = 200000
fee_denom = 'stake'
fee_amount = 10
clock_drift = '5s'
trusting_period = '14days'
```

### Adding Private Keys

For each chain configured you need to add a private key for that chain in order to submit [transactions](./commands/raw/index.md), please refer to the [Keys](./commands/keys/index.md) sections in order to learn how to add the private keys that are used by the relayer.

### Example configuration file

Here is a full example of a configuration file with two chains configured:

```toml
[global]
strategy = 'packets'
log_level = 'error'

[[chains]]
id = 'ibc-0'
rpc_addr = 'http://127.0.0.1:26657'
grpc_addr = 'http://127.0.0.1:9090'
websocket_addr = 'ws://localhost:26657/websocket'
rpc_timeout = '10s'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
gas = 200000
fee_denom = 'stake'
fee_amount = 10
clock_drift = '5s'
trusting_period = '14days'

[chains.trust_threshold]
numerator = '1'
denominator = '3'

[[chains]]
id = 'ibc-1'
rpc_addr = 'http://127.0.0.1:26557'
grpc_addr = 'http://127.0.0.1:9091'
websocket_addr = 'ws://localhost:26557/websocket'
rpc_timeout = '10s'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
gas = 200000
fee_denom = 'stake'
fee_amount = 10
clock_drift = '5s'
trusting_period = '14days'

[chains.trust_threshold]
numerator = '1'
denominator = '3'
```

### Next Steps

Now that you learned how to build the relayer and how to create a configuration file, you can go to the [`Two Chains`](./tutorials/local-chains/index.md) tutorial to learn how to perform some local testing connecting the relayer to two local chains.

[log-level]: ./help.html#parametrizing-the-log-output-level

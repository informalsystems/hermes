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

## Configuration

The configuration file must have one `global` section, and one `chains` section for each chain.

> **Note:** As of 0.6.0, the Hermes configuration file is self-documented.
> Please read the configuration file [`config.toml`](https://github.com/informalsystems/ibc-rs/blob/v0.13.0-rc.0/config.toml)
> itself for the most up-to-date documentation of parameters.

By default, Hermes will relay on all channels available between all the configured chains.
In this way, every configured chain will act as a source (in the sense that Hermes listens for events)
and as a destination (to relay packets that others chains have sent).

For example, if there are only two chains configured, then Hermes will only relay packets between those two,
i.e. the two chains will serve as a source for each other, and likewise as a destination for each other's relevant events.
Hermes will ignore all events that pertain to chains which are unknown (ie. not present in config.toml).

To restrict relaying on specific channels, or uni-directionally, you can use [packet filtering policies](https://github.com/informalsystems/ibc-rs/blob/v0.13.0-rc.0/config.toml#L207-L224).

## Adding private keys

For each chain configured you need to add a private key for that chain in order to submit [transactions](./commands/raw/index.md),
please refer to the [Keys](./commands/keys/index.md) sections in order to learn how to add the private keys that are used by the relayer.

## Example configuration file

Here is a full example of a configuration file with two chains configured:

```toml
[global]
log_level = 'info'

[mode]

[mode.clients]
enabled = true
refresh = true
misbehaviour = true

[mode.connections]
enabled = false

[mode.channels]
enabled = false

[mode.packets]
enabled = true
clear_interval = 100
clear_on_start = true
tx_confirmation = true

[rest]
enabled = true
host = '127.0.0.1'
port = 3000

[telemetry]
enabled = true
host = '127.0.0.1'
port = 3001

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
fee_granter = ''
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

Before Hermes 0.6.1, the only way to get Hermes to pick up a change in the
configuration was to stop and restart Hermes.

As of version 0.6.1, Hermes will react to receiving a `SIGHUP` signal
by reloading the `[chains]` section of the configuration, and
stopping, starting or restarting the affected workers.

> ⚠️  **Warning:** the configuration reload feature only supports
> adding, removing, or updating configuration of chains. It does
> not support dynamically changing global features, such as the
> filtering mechanism or logging level.

For example, say you start with the configuration given in the previous section
in `~/.hermes/config.toml`, ie. with two chains `ibc-0` and `ibc-1`.

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

[log-level]: ./help.md#parametrizing-the-log-output-level

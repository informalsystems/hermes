# Configuration

In order to run `Hermes`, you will need to have a configuration file.

The format supported for the configuration file is [TOML](https://toml.io/en/).

By default, `Hermes` expect the configuration file to be located at `$HOME/.hermes/config.toml`.

This can be overriden by supplying the `-c` flag when invoking hermes, before the
name of the command to run, eg. `hermes -c my_config.toml query connection channels ibc-1 connection-1`.

> With the exception of the light client configuration, current relayer does not support managing the configuration file programmatically.
> You will need to use a text editor to create the file and add content to it.

```bash
hermes [-c CONFIG_FILE] COMMAND
```

## Sections

The configuration file must have one `global` section, as well as contain one `chains` section for each chain.

### `[global]`

The global section has parameters that apply globally to the relayer operation.

#### Parameters

* __timeout__: Specify the maximum amount of time (duration) that the operations should take before timing out. Default value is `10s` (10 seconds)

* __strategy__: Specify the strategy to be used by the relayer. Currently only `naive` is supported

* __log_level__: Specify the verbosity for the relayer logging output. Valid options are 'error', 'warn', 'info', 'debug', 'trace'. Default value is `info`.

Here's an example for the `global` section:

```toml
[global]
timeout = '10s'
strategy = 'naive'
log_level = 'info'
```

### [[chains]]

A `chains` section includes parameters related to a chain and the full node to which the relayer can send transactions and  queries. It also has parameters related to the light client configuration peers for the chain.

#### Parameters

* __id__: Specify the chain ID. For example `ibc-0`

* __rpc_addr__: Specify the RPC address and port where the chain RPC server listens on. For example `tcp://localhost:26657`

* __grpc_addr__: Specify the GRPC address and port where the chain GRPC server listens on. For example `tcp://localhost:9090`

* __account_prefix__: Specify the prefix used by the chain. For example `cosmos`

* __key_name__: Specify the name of the private key JSON file. This is the filename for the private key used to sign transactions on this chain. Don't specify the file extension, for example if the filename for the private key is `testkey.json`, specify only `testkey` for this parameter.

* __store_prefix__: Specify the store prefix used by the on-chain IBC modules. For example `ibc`.

* __gas__: Specify the maximum amount of gas to be used as the gas limit for a transaction. Default value is `300000`

* __clock_drift__: Specify the maximum amount of time to tolerate a clock drift. The clock drift parameter defines how much new (untrusted) header's Time can drift into the future. Default value is `5s`

* __trusting_period__: Specify the amount of time to be used as the trusting period. It should be significantly less than the unbonding period (e.g. unbonding period = 3 weeks, trusting period = 2 weeks). Default value is `14days` (336 hours)

For example if you want to add a configuration for a chain named `ibc-0`:

```toml
[[chains]]
id = 'ibc-0'
rpc_addr = 'tcp://localhost:26657'
grpc_addr = 'tcp://localhost:9090'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
gas = 200000
clock_drift = '5s'
trusting_period = '14days'
```

### Light clients

The configuration file stores information about the light client peers. This configuration can be added to the configuration file when running the `relayer light add` relayer command. Please see the [Light Clients](./light_clients.md) section to learn how to configure them.

### Adding Private Keys

For each chain configured you need to add a private key for that chain in order to submit [transactions](./transactions.md), please refer to the [Keys](./keys.md) sections in order to learn how to add the private keys that will be used by the relayer.

### Example configuration file

Here is an full example of a configuration file with two chains configured and light client peers added:

```toml
[global]
timeout = '10s'
strategy = 'naive'
log_level = 'error'

[[chains]]
id = 'ibc-0'
rpc_addr = 'tcp://localhost:26657'
grpc_addr = 'tcp://localhost:9090'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
gas = 200000
clock_drift = '5s'
trusting_period = '14days'

[chains.trust_threshold]
numerator = '1'
denominator = '3'

[chains.peers]
primary = '66E3B7083DF9DD1FC57A611929BF4C505E34AA88'

[[chains.peers.light_clients]]
peer_id = '66E3B7083DF9DD1FC57A611929BF4C505E34AA88'
address = 'tcp://localhost:26657'
timeout = '10s'
trusted_header_hash = 'A24F654188BC3FC9EFE589FB33D513CE9AC86BFA48B063BDBF1D769750713E09'
trusted_height = '15'

[chains.peers.light_clients.store]
type = 'disk'
path = '/ibc-rs/data/ibc-0/data/66E3B7083DF9DD1FC57A611929BF4C505E34AA88'

[[chains.peers.light_clients]]
peer_id = '2427F8D914A6862279B3326FA64F76E3BC06DB2E'
address = 'tcp://localhost:26657'
timeout = '10s'
trusted_header_hash = '44E7C90BFA53256AD72B84286BFDA70FE87BBC7C0D80A1DB199C72A4FBE88FB6'
trusted_height = '16'

[chains.peers.light_clients.store]
type = 'disk'
path = '/ibc-rs/data/ibc-0/data/2427F8D914A6862279B3326FA64F76E3BC06DB2E'

[[chains]]
id = 'ibc-1'
rpc_addr = 'tcp://localhost:26557'
grpc_addr = 'tcp://localhost:9091'
account_prefix = 'cosmos'
key_name = 'testkey'
store_prefix = 'ibc'
gas = 200000
clock_drift = '5s'
trusting_period = '14days'

[chains.trust_threshold]
numerator = '1'
denominator = '3'

[chains.peers]
primary = '28ED8856CBACA85DA866AB99F50DB22A58DA35F4'

[[chains.peers.light_clients]]
peer_id = '28ED8856CBACA85DA866AB99F50DB22A58DA35F4'
address = 'tcp://localhost:26557'
timeout = '10s'
trusted_header_hash = '66BD0E5ED1FA2022A036782F7D8444DB98DC0326B379BCA6BA75864295D1C910'
trusted_height = '4'

[chains.peers.light_clients.store]
type = 'disk'
path = '/ibc-rs/data/ibc-1/data/28ED8856CBACA85DA866AB99F50DB22A58DA35F4'

[[chains.peers.light_clients]]
peer_id = 'A885BB3D3DFF6101188B462466AE926E7A6CD51E'
address = 'tcp://localhost:26557'
timeout = '10s'
trusted_header_hash = '0325BFAA36407D1F11966AEC57D34131CB27B370D3698F284F09152ADE3423C4'
trusted_height = '5'

[chains.peers.light_clients.store]
type = 'disk'
path = '/ibc-rs/data/ibc-1/data/A885BB3D3DFF6101188B462466AE926E7A6CD51E'

[[connections]]
a_chain = "ibc1"
b_chain = "ibc0"

[[connections.paths]]
a_port = 'transfer'
b_port = 'transfer'
```

### Next Steps

Now that you learned how to build the relayer and how to create a configuration file, you can go to the [`Two Chains`](./two_chains.md) tutorial to learn how to perform some local testing connecting the relayer to two local chains.

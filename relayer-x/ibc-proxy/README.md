# IBC Node Proxy

## Quick start

First follow the instructions at https://github.com/informalsystems/ibc-rs/blob/anca/ibcnode/relayer-x/README.md
to set up two chains with the PostgreSQL indexer.

### 1.Spawn node for `ibc-0`

```shell
$ RUST_LOG=debug cargo run -- --port 8220 --rpc http://localhost:26657 --db postgres://tendermint:tendermint@localhost/ibc0 --ws http://localhost:26657
```

### 2. Spawn node for `ibc-1`

```shell
$ RUST_LOG=debug cargo run -- --port 8221 --rpc http://localhost:26557 --db postgres://tendermint:tendermint@localhost/ibc1 --ws http://localhost:26557
```

### 3. Update Hermes config

In the Hermes `config.toml`, change the `rpc_addr` of both chains to

- `http://localhost:8220` for `ibc-0`
- `http://localhost:8221` for `ibc-1`

### 4. Test

Use Hermes to create a client, connection and channel between `ibc-0` and `ibc-1`:

```
$ hermes -c config.toml create channel ibc-0 -c ibc-1 --port-a transfer --port-b transfer --new-client-connection
```

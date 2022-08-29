# Parametrize the log level

This section explains how to parametrize the log output level of `hermes`.


The relayer configuration file permits parametrization of output verbosity via the knob called `log_level`.
This file is loaded by default from `$HOME/.hermes/config.toml`, but can be overridden in all commands
with the `--config` flag, e.g. `hermes --config ./path/to/my/config.toml some command`.

Relevant snippet:

```toml
[global]
log_level = 'error'
```

Valid options for `log_level` are: 'error', 'warn', 'info', 'debug', 'trace'.
These levels correspond to the tracing subcomponent of the relayer-cli,
[see here](https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html).

The relayer will _always_ print a last line summarizing the result of its
operation for queries or transactions. In addition to this last line,
arbitrary debug, info, or other outputs may be produced.


## Overriding the tracing filter using `RUST_LOG`

For debugging purposes, we may want to inspect which RPC queries the relayer is making.
The relayer makes use of the `tendermint-rpc` library to issue RPC queries, but
the output of this library is by default turned off in order to keep the logs more
readable.

Using the `RUST_LOG` environment variable, we can turn logging on for the
`tendermint-rpc` library, as follows:

```
RUST_LOG=tendermint-rpc=debug,info hermes start
```

Setting the `RUST_LOG` environment variable to `tendermint_rpc=debug,info` instructs
the relayer to set the log level of the `tendermint_rpc` crate to `debug` and otherwise
use the `info` log level.

> **Note:** While the `tendermint-rpc` contains a dash in its name, the logging filter
> expects a module name, which can only contain alphanumeric characters and underscores,
> hence why the filter above is written `tendermint_rpc=debug`.

**Example:**

```
❯ RUST_LOG=tendermint_rpc=debug,info hermes start
2022-02-24T14:32:14.039555Z  INFO ThreadId(01) using default configuration from '/Users/coromac/.hermes/config.toml'
2022-02-24T14:32:14.043500Z  INFO ThreadId(01) telemetry service running, exposing metrics at http://127.0.0.1:3001/metrics
2022-02-24T14:32:14.043542Z  INFO ThreadId(01) [rest] address not configured, REST server disabled
2022-02-24T14:32:14.049759Z DEBUG ThreadId(01) Incoming response: {
  "jsonrpc": "2.0",
  "id": "143b4580-c49e-47c1-81b2-4e7090f6e762",
  "result": {
    "node_info": {
      "protocol_version": {
        "p2p": "8",
        "block": "11",
        "app": "0"
      },
      "id": "73f9134539f9845cd253dc302e36d48ee4c0f32d",
      "listen_addr": "tcp://0.0.0.0:27003",
      "network": "ibc0",
      "version": "v0.34.14",
      "channels": "40202122233038606100",
      "moniker": "ibc0",
      "other": {
        "tx_index": "on",
        "rpc_address": "tcp://0.0.0.0:27000"
      }
    },
    "sync_info": {
      "latest_block_hash": "8396B93E355AD80EED8167A04BB9858A315A8BEB482547DE16A6CD82BC11551B",
      "latest_app_hash": "22419E041D6997EE75FF66F7F537A3D36122B220EAB89A9C246FEF680FB1C97A",
      "latest_block_height": "86392",
      "latest_block_time": "2022-02-24T14:32:08.673989Z",
      "earliest_block_hash": "0A73CFE8566D4D4FBFE3178D9BCBAD483FD689854CA8012FF1457F8EC4598132",
      "earliest_app_hash": "E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855",
      "earliest_block_height": "1",
      "earliest_block_time": "2022-01-20T09:04:21.549736Z",
      "catching_up": false
    },
    "validator_info": {
      "address": "6FD56E6AA1EEDAD227AFAB6B9DE631719D4A3691",
      "pub_key": {
        "type": "tendermint/PubKeyEd25519",
        "value": "mR5V/QWOv/mJYyNmlsl3mfxKy1PNaOzdztyas4NF2BA="
      },
      "voting_power": "10"
    }
  }
}
2022-02-24T14:32:14.052503Z DEBUG ThreadId(21) Incoming response: {
  "jsonrpc": "2.0",
  "id": "0ca35e64-ea98-4fbf-bd66-c3291128ace9",
  "result": {}
}

...
```

The two DEBUG log lines above were emitted by the `tendermint-rpc` crate.


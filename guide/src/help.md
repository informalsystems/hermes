# Help

This section provides guidelines regarding troubleshooting and general
resources for getting help with `hermes`.
For this purpose, we recommend a few ideas that could be of help:

- [hermes help][help] command, providing a CLI
  documentation for all `hermes` commands.
- [profile][profiling] your relayer binary to identify slow methods;
- [configure][log-level] the `log_level` to help with debugging;
- [patch][patching] your local gaia chain(s) to enable some corner-case methods
  (e.g., channel close);

And if the above options do not address your specific problem:
- you can [request a new feature][feature];
- or consult the [list of reported issues][issues] and search by relevant
  keywords to see if you're dealing with a known problem;
- we would be grateful if you can submit a [bug report][bug-report]
  discussing any problem you find, and from there on we can look at the
  problem together;

Lastly, for general questions, you can reach us at `hello@informal.systems`,
or on Twitter [@informalinc][twitter].

## Table of contents

<!-- toc -->

## Help command

The CLI comprises a special `help` command, which accepts as parameter other commands, and provides guidance on what is the correct way to invoke those commands.

For instance,

```shell
hermes help create
```

will provide details about all the valid invocations of the `create` CLI command.

```
USAGE:
    hermes create <SUBCOMMAND>

DESCRIPTION:
    Create objects (client, connection, or channel) on chains

SUBCOMMANDS:
    help       Get usage information
    client     Create a new IBC client
    connection Create a new connection between two chains
    channel    Create a new channel between two chains
```

This can provide further specific guidance if we add additional parameters, e.g., 

```shell
hermes help create channel
```

```
USAGE:
    hermes create channel <OPTIONS>

DESCRIPTION:
    Create a new channel between two chains

POSITIONAL ARGUMENTS:
    chain_a_id                identifier of the side `a` chain for the new channel
    chain_b_id                identifier of the side `b` chain for the new channel (optional)

FLAGS:
    -c, --connection-a CONNECTION-A
    --port-a PORT-A           identifier of the side `a` port for the new channel
    --port-b PORT-B           identifier of the side `b` port for the new channel
    -o, --order ORDER         the channel ordering, valid options 'unordered' (default) and 'ordered'
    -v, --channel-version VERSION     the version for the new channel
```

Additionally, the `-h`/`--help` flags typical for CLI applications work on
all commands.

## Parametrizing the log output level

The relayer configuration file permits parametrization of output verbosity via the knob called `log_level`.
This file is loaded by default from `$HOME/.hermes/config.toml`, but can be overridden in all commands
with the `-c` flag, eg. `hermes -c ./path/to/my/config.toml some command`.

Relevant snippet:

```toml
[global]
log_level = 'error'
```

Valid options for `log_level` are: 'error', 'warn', 'info', 'debug', 'trace'.
These levels correspond to the tracing sub-component of the relayer-cli,
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

## Inspecting the relayer state

To get a little bit of insight into the state of the relayer,
Hermes will react to a `SIGUSR1` signal by dumping its state to
the console, either in plain text form or as a JSON object if Hermes
was started with the `--json` option.

To send a `SIGUSR1` signal to Hermes, look up its process ID (below PID)
and use the following command:

```shell
kill -SIGUSR1 PID
```

Hermes will print some information about the workers which are currently running.

For example, with three chains configured and one channel between each pair of chains:

```text
INFO Dumping state (triggered by SIGUSR1)
INFO
INFO * Chains: ibc-0, ibc-1, ibc-2
INFO * Client workers:
INFO   - client::ibc-0->ibc-1:07-tendermint-0 (id: 5)
INFO   - client::ibc-0->ibc-2:07-tendermint-0 (id: 9)
INFO   - client::ibc-1->ibc-0:07-tendermint-0 (id: 1)
INFO   - client::ibc-1->ibc-2:07-tendermint-1 (id: 11)
INFO   - client::ibc-2->ibc-0:07-tendermint-1 (id: 3)
INFO   - client::ibc-2->ibc-1:07-tendermint-1 (id: 7)
INFO * Packet workers:
INFO   - packet::channel-0/transfer:ibc-0->ibc-1 (id: 2)
INFO   - packet::channel-0/transfer:ibc-1->ibc-0 (id: 6)
INFO   - packet::channel-0/transfer:ibc-2->ibc-0 (id: 10)
INFO   - packet::channel-1/transfer:ibc-0->ibc-2 (id: 4)
INFO   - packet::channel-1/transfer:ibc-1->ibc-2 (id: 8)
INFO   - packet::channel-1/transfer:ibc-2->ibc-1 (id: 12)
```

or in JSON form (prettified):

```json
{
  "timestamp": "Jul 12 17:04:37.244",
  "level": "INFO",
  "fields": {
    "message": "Dumping state (triggered by SIGUSR1)"
  }
}
{
  "chains": [
    "ibc-0",
    "ibc-1",
    "ibc-2"
  ],
  "workers": {
    "Client": [
      {
        "id": 5,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-1",
          "dst_client_id": "07-tendermint-0",
          "src_chain_id": "ibc-0"
        }
      },
      {
        "id": 9,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-2",
          "dst_client_id": "07-tendermint-0",
          "src_chain_id": "ibc-0"
        }
      },
      {
        "id": 1,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-0",
          "dst_client_id": "07-tendermint-0",
          "src_chain_id": "ibc-1"
        }
      },
      {
        "id": 11,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-2",
          "dst_client_id": "07-tendermint-1",
          "src_chain_id": "ibc-1"
        }
      },
      {
        "id": 3,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-0",
          "dst_client_id": "07-tendermint-1",
          "src_chain_id": "ibc-2"
        }
      },
      {
        "id": 7,
        "object": {
          "type": "Client",
          "dst_chain_id": "ibc-1",
          "dst_client_id": "07-tendermint-1",
          "src_chain_id": "ibc-2"
        }
      }
    ],
    "Packet": [
      {
        "id": 2,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-1",
          "src_chain_id": "ibc-0",
          "src_channel_id": "channel-0",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 6,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-0",
          "src_chain_id": "ibc-1",
          "src_channel_id": "channel-0",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 10,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-0",
          "src_chain_id": "ibc-2",
          "src_channel_id": "channel-0",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 4,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-2",
          "src_chain_id": "ibc-0",
          "src_channel_id": "channel-1",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 8,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-2",
          "src_chain_id": "ibc-1",
          "src_channel_id": "channel-1",
          "src_port_id": "transfer"
        }
      },
      {
        "id": 12,
        "object": {
          "type": "Packet",
          "dst_chain_id": "ibc-1",
          "src_chain_id": "ibc-2",
          "src_channel_id": "channel-1",
          "src_port_id": "transfer"
        }
      }
    ]
  }
}
```

## Patching `gaia` to support `ChanCloseInit`

The guide below refers specifically to patching your gaia chain so that the
relayer can initiate the closing of channels by submitting a [`ChanCloseInit`][chan-close] message.
Without this modification, the transaction will be rejected.
We also describe how to test the channel closing feature.

- Clone the Cosmos SDK

    ```shell
    git clone https://github.com/cosmos/cosmos-sdk.git ~/go/src/github.com/cosmos/cosmos-sdk
    cd ~/go/src/github.com/cosmos/cosmos-sdk
    ```

- Apply these diffs:

    ```
       --- a/x/ibc/applications/transfer/module.go
       +++ b/x/ibc/applications/transfer/module.go
       @@ -305,7 +305,7 @@ func (am AppModule) OnChanCloseInit(
               channelID string,
        ) error {
               // Disallow user-initiated channel closing for transfer channels
       -       return sdkerrors.Wrap(sdkerrors.ErrInvalidRequest, "user cannot close channel")
       +       return nil
        }
    ```

- Append the line below (watch for the placeholder `<your>`) as the last line
  in your `go.mod` in the gaia clone:

```replace github.com/cosmos/cosmos-sdk => /Users/<your>/go/src/github.com/cosmos/cosmos-sdk```

- Now `make build` and `make install` your local copy of gaia

In order to test the correct operation during the channel close, perform the steps below.

- the channel should be in state open-open:

- transfer of 5555 samoleans from `ibc-1` to `ibc-0`. This results in a
  Tx to `ibc-1` for a `MsgTransfer` packet.
  Make sure you're not relaying this packet (the relayer should not be running on
  this path).

  ```shell
  hermes tx raw ft-transfer ibc-0 ibc-1 transfer channel-1 5555 -o 1000 -n 1 -d samoleans
  ```

- now do the first step of channel closing: the channel will transition
to close-open:

    ```shell
    hermes -c config.toml tx raw chan-close-init ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-1
    ```

- trigger timeout on close to ibc-1

    ```shell
    hermes -c config.toml tx raw packet-recv ibc-0 ibc-1 transfer channel-1
    ```

- close-close

    ```shell
    hermes -c config.toml tx raw chan-close-confirm ibc-1 ibc-0 connection-1 transfer transfer channel-1 channel-0
    ```

- verify that the two ends are in Close state:

  ```shell
  hermes -c config.toml query channel end ibc-0 transfer channel-0
  hermes -c config.toml query channel end ibc-1 transfer channel-1
  ```


## New Feature Request

If you would like a feature to be added to `hermes`, don't hesitate
to open a discussion about that via the [feature request][feature-request]
issue template.

> Note that Hermes is packaged as part of the `ibc-relayer-cli` crate.


## Profiling

The `relayer` crate provides a `time!` macro which can be used to measure how much time is spent between the invocation of the macro and the end of the enclosing scope.

### Setup

The `time!` macro has no effect unless the `profiling` feature of the `relayer` crate is enabled.

To enable it, one must compile the `relayer-cli` crate with the `--features=profiling` flag.

a) One way is to build the `relayer` binary and update the `hermes` alias to point to the executable:

```shell
cd relayer-cli/
cargo build --features=profiling
```

b) Alternatively, one can use the `cargo run` command and update the alias accordingly:

```shell
alias hermes='cargo run --features=profiling --manifest-path=relayer-cli/Cargo.toml --'
```

The `--manifest-path=relayer-cli/Cargo.toml` flag is needed for `cargo run` to accept the `--features` flag.

### Example

```rust
fn my_function(x: u32) -> u32 {
    time!("myfunction: x={}", x); // A

    std::thread::sleep(Duration::from_secs(1));

    {
        time!("inner operation"); // B

        std::thread::sleep(Duration::from_secs(2));

        // timer B ends here
    }

    x + 1

    // timer A ends here
}
```

#### Output

```
Jan 20 11:28:46.841  INFO relayer::macros::profiling: ⏳ myfunction: x=42 - start
Jan 20 11:28:47.842  INFO relayer::macros::profiling:    ⏳ inner operation - start
Jan 20 11:28:49.846  INFO relayer::macros::profiling:    ⏳ inner operation - elapsed: 2004ms
Jan 20 11:28:49.847  INFO relayer::macros::profiling: ⏳ myfunction: x=42 - elapsed: 3005ms
```

Profiling is useful for tracking down unusually slow methods.
Each transaction or query usually consists of multiple lower-level methods,
and it's often not clear which of these are the culprit for low performance.
With profiling enabled, `hermes` will output timing information for individual
methods involved in a command.

__NOTE__: To be able to see the profiling output, the realyer needs to be compiled with
the `profiling` feature and the [log level][log-level] should be `info` level or lower.

#### Example output for `tx raw conn-init` command

```
hermes -c   config.toml tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-0
```

```
Apr 13 20:58:21.225  INFO ibc_relayer::macros::profiling: ⏳ init_light_client - start
Apr 13 20:58:21.230  INFO ibc_relayer::macros::profiling: ⏳ init_light_client - elapsed: 4ms
Apr 13 20:58:21.230  INFO ibc_relayer::macros::profiling: ⏳ init_event_monitor - start
Apr 13 20:58:21.235  INFO ibc_relayer::macros::profiling: ⏳ init_event_monitor - elapsed: 5ms
Apr 13 20:58:21.235  INFO ibc_relayer::event::monitor: running listener chain.id=ibc-1
Apr 13 20:58:21.236  INFO ibc_relayer::macros::profiling: ⏳ init_light_client - start
Apr 13 20:58:21.239  INFO ibc_relayer::macros::profiling: ⏳ init_light_client - elapsed: 2ms
Apr 13 20:58:21.239  INFO ibc_relayer::macros::profiling: ⏳ init_event_monitor - start
Apr 13 20:58:21.244  INFO ibc_relayer::macros::profiling: ⏳ init_event_monitor - elapsed: 4ms
Apr 13 20:58:21.244  INFO ibc_relayer::event::monitor: running listener chain.id=ibc-0
Apr 13 20:58:21.244  INFO ibc_relayer::macros::profiling: ⏳ get_signer - start
Apr 13 20:58:21.246  INFO ibc_relayer::macros::profiling: ⏳ get_signer - elapsed: 1ms
Apr 13 20:58:21.246  INFO ibc_relayer::macros::profiling: ⏳ query_latest_height - start
Apr 13 20:58:21.246  INFO ibc_relayer::macros::profiling:    ⏳ block_on - start
Apr 13 20:58:21.248  INFO ibc_relayer::macros::profiling:    ⏳ block_on - elapsed: 1ms
Apr 13 20:58:21.249  INFO ibc_relayer::macros::profiling: ⏳ query_latest_height - elapsed: 3ms
Apr 13 20:58:21.250  INFO ibc_relayer::macros::profiling: ⏳ unbonding_period - start
Apr 13 20:58:21.250  INFO ibc_relayer::macros::profiling:    ⏳ block_on - start
Apr 13 20:58:21.251  INFO ibc_relayer::macros::profiling:    ⏳ block_on - elapsed: 0ms
Apr 13 20:58:21.270  INFO ibc_relayer::macros::profiling:    ⏳ block_on - start
Apr 13 20:58:21.273  INFO ibc_relayer::macros::profiling:    ⏳ block_on - elapsed: 2ms
Apr 13 20:58:21.273  INFO ibc_relayer::macros::profiling: ⏳ unbonding_period - elapsed: 23ms
Apr 13 20:58:21.279  INFO ibc_relayer::macros::profiling: ⏳ build_consensus_state - start
Apr 13 20:58:21.280  INFO ibc_relayer::macros::profiling: ⏳ build_consensus_state - elapsed: 0ms
Apr 13 20:58:21.280  INFO ibc_relayer::macros::profiling: ⏳ send_msgs - start
Apr 13 20:58:21.280  INFO ibc_relayer::macros::profiling:    ⏳ send_tx - start
Apr 13 20:58:21.282  INFO ibc_relayer::macros::profiling:       ⏳ PK "03f17d2c094ee68cfcedb2c2f2b7dec6cd82ea158ac1c32d3de0ca8b288a3c8bfa" - start
Apr 13 20:58:21.282  INFO ibc_relayer::macros::profiling:          ⏳ block_on - start
Apr 13 20:58:21.285  INFO ibc_relayer::macros::profiling:          ⏳ block_on - elapsed: 3ms
Apr 13 20:58:21.296  INFO ibc_relayer::macros::profiling:             ⏳ block_on - start
Apr 13 20:58:22.664  INFO ibc_relayer::macros::profiling:             ⏳ block_on - elapsed: 1367ms
Apr 13 20:58:22.664  INFO ibc_relayer::macros::profiling:       ⏳ PK "03f17d2c094ee68cfcedb2c2f2b7dec6cd82ea158ac1c32d3de0ca8b288a3c8bfa" - elapsed: 1382ms
Apr 13 20:58:22.664  INFO ibc_relayer::macros::profiling:    ⏳ send_tx - elapsed: 1384ms
Apr 13 20:58:22.664  INFO ibc_relayer::macros::profiling: ⏳ send_msgs - elapsed: 1384ms
Success: CreateClient(
    CreateClient(
        Attributes {
            height: Height {
                revision: 0,
                height: 10675,
            },
            client_id: ClientId(
                "07-tendermint-7",
            ),
            client_type: Tendermint,
            consensus_height: Height {
                revision: 1,
                height: 10663,
            },
        },
    ),
)
```



[help]: ./help.md#help-command
[feature-request]: https://github.com/informalsystems/ibc-rs/issues/new?assignees=&labels=&template=feature-request.md
[bug-report]: https://github.com/informalsystems/ibc-rs/issues/new?assignees=&labels=&template=bug-report.md
[twitter]: https://twitter.com/informalinc
[twitter-image]: https://abs.twimg.com/errors/logo23x19.png
[website]: https://informal.systems
[log-level]: ./help.md#parametrizing-the-log-output-level
[issues]: https://github.com/informalsystems/ibc-rs/issues
[profiling]: ./help.md#profiling
[feature]: ./help.md#new-feature-request
[patching]: ./help.md#patching-gaia
[chan-close]: ./commands/raw/channel-close.md#channel-close-init

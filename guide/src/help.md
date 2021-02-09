# Help

This section provides guidelines regarding troubleshooting and general
resources for getting help with `hermes`.
For this purpose, we recommend a few ideas that could be of help:

- [profile][profiling] your relayer binary to identify slow methods;
- [configure][log-level] the `log_level` to help with debugging;
- [patch][patching] your local gaia chain(s) to enable some corner-case methods
  (e.g., channel close);

And if the above do not help:
- you can [request a new feature][feature];
- or consult the [list of reported issues][issues] and search by relevant
  keywords to see if you're dealing with a known problem;
- we would be grateful if you can submit a [bug report][bug-report]
  discussing any problem you find, and from there on we can look at the
  problem together;

Lastly, for general questions, you can reach us at `hello@informal.systems`,
or on Twitter [@informalinc][twitter].

## Profiling

The `relayer` crate provides a `time!` macro which can be used to measure how much time is spent between the invocation of the macro and the end of the enclosing scope.

### Setup

The `time!` macro has no effect unless the `profiling` feature of the `relayer` crate is enabled.

To enable it, one must compile the `relayer-cli` crate with the `--features=profiling` flag.

a) One way is to build the `relayer` binary and update the `hermes` alias to point to the executable:

```shell script
cd relayer-cli/
cargo build --features=profiling
```

b) Alternatively, one can use the `cargo run` command and update the alias accordingly:

```shell script
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

__NOTE__: To be able to see the profiling output, the
[log level][log-level] should be `info`
level or lower.

#### Example output for `tx raw conn-init` command


```
hermes -c config_example.toml tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-0
{"timestamp":"Feb 03 14:46:55.282","level":"INFO","fields":{"message":"⏳ init_light_client - start"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.361","level":"INFO","fields":{"message":"⏳ init_light_client - elapsed: 75ms"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.361","level":"INFO","fields":{"message":"⏳ init_event_monitor - start"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.374","level":"INFO","fields":{"message":"⏳ init_event_monitor - elapsed: 12ms"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.374","level":"INFO","fields":{"message":"running listener","chain.id":"ibc-1"},"target":"ibc_relayer::event::monitor"}
{"timestamp":"Feb 03 14:46:55.375","level":"INFO","fields":{"message":"⏳ init_light_client - start"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.405","level":"INFO","fields":{"message":"⏳ init_light_client - elapsed: 29ms"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.405","level":"INFO","fields":{"message":"⏳ init_event_monitor - start"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.408","level":"INFO","fields":{"message":"⏳ init_event_monitor - elapsed: 3ms"},"target":"ibc_relayer::macros::profiling"}
{"timestamp":"Feb 03 14:46:55.408","level":"INFO","fields":{"message":"running listener","chain.id":"ibc-0"},"target":"ibc_relayer::event::monitor"}
{"timestamp":"Feb 03 14:46:55.410","level":"INFO","fields":{"message":"Message ConnOpenInit: Connection { a_side: ConnectionSide { chain: ProdChainHandle { chain_id: ChainId { id: \"ibc-1\", version: 1 }, runtime_sender: Sender { .. } }, client_id: ClientId(\"07-tendermint-0\"), connection_id: ConnectionId(\"defaultConnection\") }, b_side: ConnectionSide { chain: ProdChainHandle { chain_id: ChainId { id: \"ibc-0\", version: 0 }, runtime_sender: Sender { .. } }, client_id: ClientId(\"07-tendermint-0\"), connection_id: ConnectionId(\"defaultConnection\") } }"},"target":"ibc_relayer_cli::commands::tx::connection"}

```

## Parametrizing the log output level

The relayer configuration file permits parametrization of output verbosity via the knob called `log_level`.
This file is loaded by default from `$HOME/.hermes/config.toml`, but can be overridden in all commands
with the `-c` flag, eg. `hermes -c ./path/to/my/config.toml some command`.

Relevant snippet:

```toml
[global]
timeout = '10s'
strategy = 'naive'
log_level = 'error'
```

Valid options for `log_level` are: 'error', 'warn', 'info', 'debug', 'trace'.
These levels correspond to the tracing sub-component of the relayer-cli, [see
here](https://docs.rs/tracing-core/0.1.17/tracing_core/struct.Level.html).

The relayer will _always_ print a last line summarizing the result of its
operation for queries of transactions. In addition to  this last line,
arbitrary debug, info, or other outputs may be produced.  Example, with
`log_level = 'debug'`:

```bash
Running `target/debug/relayer query client consensus ibc-0 07-tendermint-X 0 1`
{"timestamp":"Jan 20 19:21:52.070","level":"DEBUG","fields":{"message":"registered component: abscissa_core::terminal::component::Terminal (v0.5.2)"},"target":"abscissa_core::component::registry"}
{"timestamp":"Jan 20 19:21:52.071","level":"DEBUG","fields":{"message":"registered component: relayer_cli::components::Tracing (v0.0.6)"},"target":"abscissa_core::component::registry"}
{"timestamp":"Jan 20 19:21:52.078","level":"INFO","fields":{"message":"Options QueryClientConsensusOptions { client_id: ClientId(\"07-tendermint-X\"), revision_number: 0, revision_height: 1, height: 0, proof: true }"},"target":"relayer_cli::commands::query::client"}
{"timestamp":"Jan 20 19:21:52.080","level":"DEBUG","fields":{"message":"resolving host=\"localhost\""},"target":"hyper::client::connect::dns"}
{"timestamp":"Jan 20 19:21:52.083","level":"DEBUG","fields":{"message":"connecting to [::1]:26657"},"target":"hyper::client::connect::http"}
{"timestamp":"Jan 20 19:21:52.083","level":"DEBUG","fields":{"message":"connecting to 127.0.0.1:26657"},"target":"hyper::client::connect::http"}
{"status":"error","result":["query error: RPC error to endpoint tcp://localhost:26657: error trying to connect: tcp connect error: Connection refused (os error 61) (code: 0)"]}
```

For the same command, with `log_level = 'error'`, just the last line will be
produced:

```bash
   Running `target/debug/relayer query client consensus ibc-0 07-tendermint-X 0 1`
{"status":"error","result":["query error: RPC error to endpoint tcp://localhost:26657: error trying to connect: tcp connect error: Connection refused (os error 61) (code: 0)"]}
```

## Patching `gaia`

The guide below refers specifically to patching your gaia chain so that the
relayer can initiate the closing of channels by submitting a [`chan-close-init`
transaction][chan-close].
Without this modification, the transaction will be rejected.
We also describe how to test the channel closing feature.

- Clone the Cosmos SDK

    ```shell script
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

  ```shell script
  hermes tx raw ft-transfer ibc-1 ibc-0 transfer channel-1 5555 1000 -n 1 -d samoleans
  ```

- now do the first step of channel closing: the channel will transition
to close-open:

    ```shell script
    hermes -c config.toml tx raw chan-close-init ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-1
    ```

- trigger timeout on close to ibc-1

    ```shell script
    hermes -c config.toml tx raw packet-recv ibc-0 ibc-1 transfer channel-1
    ```

- close-close

    ```shell script
    hermes -c config.toml tx raw chan-close-confirm ibc-1 ibc-0 connection-1 transfer transfer channel-1 channel-0
    ```

- verify that the two ends are in Close state:

  ```shell script
  hermes -c config.toml query channel end ibc-0 transfer channel-0
  hermes -c config.toml query channel end ibc-1 transfer channel-1
  ```

## New Feature Request

If you would like a feature to be added to `hermes`, don't hesitate
to open a discussion about that via the [feature request][feature-request]
issue template.

> Note that Hermes is packaged as part of the `ibc-relayer-cli` crate.

[feature-request]: https://github.com/informalsystems/ibc-rs/issues/new?assignees=&labels=&template=feature-request.md
[bug-report]: https://github.com/informalsystems/ibc-rs/issues/new?assignees=&labels=&template=bug-report.md
[twitter]: https://twitter.com/informalinc
[twitter-image]: https://abs.twimg.com/errors/logo23x19.png
[website]: https://informal.systems
[log-level]: ./help.html#parametrizing-the-log-output-level
[issues]: https://github.com/informalsystems/ibc-rs/issues
[profiling]: ./help.md#profiling
[feature]: ./help.html#new-feature-request
[patching]: ./help.html#patching-gaia
[chan-close]: ./tx_channel_close.html#channel-close-init

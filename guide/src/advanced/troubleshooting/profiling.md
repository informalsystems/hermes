# Profiling

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

#### Example output for `tx conn-init` command

```
hermes --config config.toml tx conn-init --b-chain ibc-0 --a-chain ibc-1 --b-client 07-tendermint-0 --a-client 07-tendermint-0
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

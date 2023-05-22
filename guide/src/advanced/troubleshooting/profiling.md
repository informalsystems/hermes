# Profiling

The `relayer` crate provides a `time!` macro which can be used to measure how much time is spent between the invocation of the macro and the end of the enclosing scope.

### Setup

The `time!` macro has no effect unless the `--debug=profiling` global flag is specified on the command-line:

```shell
$ hermes --debug=profiling start
```

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

#### Console output

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

__NOTE__: To be able to see the profiling output, the [log level][log-level] should be `info` level or lower.

##### Example output for `tx conn-init` command

```
{{#template ../../templates/commands/hermes/tx/conn-init_1.md DST_CHAIN_ID=ibc-0 SRC_CHAIN_ID=ibc-1 DST_CLIENT_ID=07-tendermint-0 SRC_CLIENT_ID=07-tendermint-0}}
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

#### JSON output

Additionally, if the `--debug=profiling-json` flag is specified, Hermes will output profiling information in
JSON format in a file named `hermes-YYYY-MM-DD-HHMMSS-prof.json`, in the directory specified in the `PROFILING_DIR`
env variable, or the current directory otherwise.

```json
{"name":"fetch_node_info","src_chain":"ibc-0","elapsed":6}
{"name":"chain_status","src_chain":"ibc-0","elapsed":12}
{"name":"query_config_params","src_chain":"ibc-0","elapsed":3}
{"name":"min_gas_price","src_chain":"ibc-0","elapsed":3}
{"name":"query_staking_params","src_chain":"ibc-0","elapsed":159}
{"name":"historical_entries","src_chain":"ibc-0","elapsed":329}
{"name":"query_staking_params","src_chain":"ibc-0","elapsed":121}
{"name":"unbonding_period","src_chain":"ibc-0","elapsed":12}
{"name":"query_latest_height","src_chain":"ibc-0","elapsed":8}
{"name":"fetch_node_info","src_chain":"ibc-1","elapsed":9}
{"name":"chain_status","src_chain":"ibc-1","elapsed":43}
```

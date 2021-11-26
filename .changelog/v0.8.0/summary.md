This is the final release of version 0.8.0, which now depends on the official releases of the `prost` and `tonic` crates.
In addition to everything that's included in v0.8.0-pre.1, this release updates the minimum supported Rust version to 1.56,
and contains various bug fixes and performance improvements which make the relayer more reliable.

#### Notice for operators
A new setting was added to the Hermes configuration: `max_block_time`.
This setting specifies the maximum time per block for this chain.
The block time together with the clock drift are added to the source drift to estimate
the maximum clock drift when creating a client on this chain.
For Cosmos-SDK chains a good approximation is `timeout_propose` + `timeout_commit`

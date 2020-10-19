# ibc-proto-compiler

The `ibc-proto-compiler` is a simple command-line tool to automate the compilation of [Protocol Buffers](https://developers.google.com/protocol-buffers) message definitions from the [Cosmos SDK](https://github.com/cosmos/cosmos-sdk) to Rust source code with [Prost](https://lib.rs/crates/prost), for use in the [`ibc-proto` crate](https://lib.rs/crates/ibc-proto) in the [`ibc-rs` project](https://github.com/informalsystems/ibc-rs/).

## Usage

From within the `proto-compiler` directory, run the following command to clone the Cosmos SDK repository, generate the Rust sources from the Protobuf definitions, and copy them to the `ibc-proto` crate within the `ibc-rs` project:

```bash
$ cargo run
```

The path to the Cosmos SDK checkout can be specified with the `SDK_DIR` environment variable: (default: `target/cosmos-sdk/`)

```bash
$ SDK_DIR=$HOME/Code/cosmos-sdk cargo run
```

The directory to which the Rust sources should be generated in before being copied to the appropriate location can be specified with the `OUT_DIR` environment variable: (default: temporary directory via the `tempdir` crate)

```bash
$ OUT_DIR=/tmp/rust cargo run
```

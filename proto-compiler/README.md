# ibc-proto-compiler

The `ibc-proto-compiler` is a simple command-line tool to automate the compilation of [Protocol Buffers](https://developers.google.com/protocol-buffers) message definitions from the [Cosmos SDK](https://github.com/cosmos/cosmos-sdk) to Rust source code with [Prost](https://lib.rs/crates/prost), for use in the [`ibc-proto` crate](https://lib.rs/crates/ibc-proto) in the [`ibc-rs` project](https://github.com/informalsystems/ibc-rs/).

## Usage

From within the `proto-compiler` directory, run the following command to clone the Cosmos SDK repository:

```bash
$ cargo run -- clone-sdk --commit ce3994020a0d5c246016c8832ba4a668e8b7c77b --out /tmp/sdk
```

To generate the Rust sources from the Protobuf definitions, and copy them to the `src/prost` folder `ibc-proto` crate within the `ibc-rs` project:

```bash
$ cargo run -- compile --sdk /tmp/sdk --out ../proto/src/prost
```


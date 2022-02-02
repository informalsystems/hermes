# ibc-proto-compiler

The `ibc-proto-compiler` is a simple command-line tool to automate the compilation of [Protocol Buffers](https://developers.google.com/protocol-buffers) message definitions from the [Cosmos SDK](https://github.com/cosmos/cosmos-sdk) and [IBC-Go](https://github.com/cosmos/ibc-go) to Rust source code with [Prost](https://lib.rs/crates/prost), for use in the [`ibc-proto` crate](https://lib.rs/crates/ibc-proto) in the [`ibc-rs` project](https://github.com/informalsystems/ibc-rs/).

## Usage

### Clone the Cosmos SDK

From within the `proto-compiler` directory, compile the binary using the `--locked` flag:

```bash
cargo build --locked
```

Run the following command to clone the Cosmos SDK and the IBC-Go repositories, and check out a specific commit:

```bash
cargo run -- clone --out /tmp/cosmos --sdk-commit b75c29fc15d3320ec0c7596dbd7c787c48dccad8 --ibc-go-commit 7cd110e8e58b84a283af8abe0af6eade6a0126b9
```

Note:
- the full commit hash must be specified
- the option `--ibc-go-commit` is not mandatory: if skipped, then the IBC go repository is omitted.
- ideally make sure the target directory `/tmp/cosmos` is empty

Alternatively, one can check out a tag for the Cosmos SDK with the `--sdk-tag` option:

```bash
cargo run -- clone --out /tmp/cosmos --sdk-tag v0.44.3 --ibc-go-commit 7cd110e8e58b84a283af8abe0af6eade6a0126b9
```

### Generate Rust sources from Protobuf definitions

To generate the Rust sources from the Protobuf definitions, and copy them to the `src/prost` folder `ibc-proto` crate within the `ibc-rs` project:

```bash
cargo run -- compile --sdk /tmp/cosmos/sdk --ibc /tmp/cosmos/ibc --out ../proto/src/prost
```

Note: the `--ibc` option is not mandatory; if omitted, then the IBC .proto files from the SDK repository will be used


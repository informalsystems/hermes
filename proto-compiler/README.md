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
$ cargo run -- clone --out /tmp/cosmos --sdk-commit 21814558eaa47b018018711e5fe16e0b16811fce --ibc-go-commit 333c1f338b2a14a1928a6f8ab64c37123c0e97b6
```

Note: the full commit hash must be specified.

Alternatively, one can check out a tag for the Cosmos SDK with the `--sdk-tag` option:

```bash
$ cargo run -- clone --out /tmp/cosmos --sdk-tag v0.42.1 --ibc-commit 333c1f338b2a14a1928a6f8ab64c37123c0e97b6
```

### Generate Rust sources from Protobuf definitions

To generate the Rust sources from the Protobuf definitions, and copy them to the `src/prost` folder `ibc-proto` crate within the `ibc-rs` project:

```bash
$ cargo run -- compile --sdk /tmp/cosmos/sdk --ibc /tmp/cosmos/ibc --out ../proto/src/prost
```

Additionally, this command will output the commit hash at which the Cosmos SDK is checked out into `$out/COSMOS_SDK_COMMIT`.

This value is exposed via the `ibc_proto::COSMOS_SDK_VERSION` constant in the `ibc-proto` library.

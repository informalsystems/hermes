# ibc-proto-compiler

The `ibc-proto-compiler` is a simple command-line tool to automate the compilation of [Protocol Buffers](https://developers.google.com/protocol-buffers) message definitions from the [Cosmos SDK](https://github.com/cosmos/cosmos-sdk) to Rust source code with [Prost](https://lib.rs/crates/prost), for use in the [`ibc-proto` crate](https://lib.rs/crates/ibc-proto) in the [`ibc-rs` project](https://github.com/informalsystems/ibc-rs/).

## Usage

### Clone the Cosmos SDK

From within the `proto-compiler` directory, run the following command to clone the Cosmos SDK repository, and check out a specific commit:

```bash
$ cargo run -- clone-sdk --out /tmp/sdk --commit 15324920548c2629e51d837bcefc1cbc40797c5d
```

Note: the full commit hash must be specified.

Alternatively, one can check out a tag with the `--tag` option:

```bash
$ cargo run -- clone-sdk --out /tmp/sdk --tag v0.39.1-rc3 
```

If neither `--commit` nor `--tag` is specified, then the default main branch will be checked out.

### Generate Rust sources from Protubuf definitions

To generate the Rust sources from the Protobuf definitions, and copy them to the `src/prost` folder `ibc-proto` crate within the `ibc-rs` project:

```bash
$ cargo run -- compile --sdk /tmp/sdk --out ../proto/src/prost
```

Additionally, this command will output the commit hash at which the Cosmos SDK is checked out into `$out/COSMOS_SDK_COMMIT`.

This value is exposed via the `ibc_proto::COSMOS_SDK_VERSION` constant in the `ibc-proto` library.

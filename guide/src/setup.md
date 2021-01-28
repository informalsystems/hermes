# Building the Relayer

In order to build and run the relayer, please follow the steps below:

> NOTE: This assumes you have installed all the [pre-requisites](./pre-requisites.md) on your machine.

### Clone the repository

Open a terminal and clone the repository:

```shell
git clone https://github.com/informalsystems/ibc-rs.git`
```

Change to the repository directory
```shell
cd ibc-rs
```

### Checkout the latest release

Go to the [ibc-rs releases](https://github.com/informalsystems/ibc-rs/releases) page to see what is the most recent release.

Then checkout the release, for example if the most recent release is `v0.1.0` then execute the command:

```shell
git checkout v0.1.0
```

### Building with `cargo build`

This command will build all the projects from the [__`ibc-rs`__](https://github.com/informalsystems/ibc-rs) repository including the [__`IBC modules`__](https://github.com/informalsystems/ibc-rs/tree/master/modules) crate, [__`relayer`__](https://github.com/informalsystems/ibc-rs/tree/master/relayer) crate, [__`proto`__](https://github.com/informalsystems/ibc-rs/tree/master/proto) crate, and the [__`relayer-cli`__](https://github.com/informalsystems/ibc-rs/tree/master/relayer-cli) tool.

```shell
cargo build --workspace --all --release
```

If the build is successful, the `relayer` executable will be located in the following location:

```shell
./target/release/relayer
```

### Running for the first time

If you run the `relayer` without any additional parameters you should see the usage and help information:

```shell
$ ./target/release/relayer
relayer-cli 0.1.0
Informal Systems <hello@informal.systems>

USAGE:
    relayer-cli <SUBCOMMAND>

SUBCOMMANDS:
    help       get usage information
    start      start the relayer (currently this refers to the v0 relayer)
    listen     listen to IBC events
    config     manipulate the relayer configuration
    version    display version information
    query      query state from chain
    tx         create IBC transactions on configured chains
    light      basic functionality for managing the lite clients
    keys       manage keys in the relayer for each chain
```

### Next Steps

Next, go to the [`Configuration`](./config.md) section to learn how to create a configuration file to be used by the relayer.
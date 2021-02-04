# Install the relayer

In order to install and run Hermes, please follow the steps below:

> NOTE: This assumes you have installed all the [pre-requisites](./pre_requisites.md) on your machine.

## Install via Cargo

Hermes is packaged in the `ibc-relayer-cli` Rust crate.
To install the latest release of Hermes, run the following command in a terminal:

```shell
cargo install ibc-relayer-cli
```

This will download and build the crate `ibc-relayer-cli`, and install the 
`hermes` binary in `$HOME/.cargo/bin`.

> If you have not installed Rust and Cargo via [rustup.rs](https://rustup.rs), you may need to
> add the `$HOME/.cargo/bin` directory to your `PATH` environment variable.
> For most shells, this can be done by adding the following line to your
> `.bashrc` or `.zshrc` configuration file:
>
> ```shell
> export PATH="$HOME/.cargo/bin:$PATH"
> ```

You should now be able to run Hermes by invoking the `hermes` executable.

```shell
hermes version
hermes 0.1.0
```

## Build from source

### Clone the repository

Open a terminal and clone the following `ibc-rs` repository:

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

This command builds all the crates from the [__`ibc-rs`__](https://github.com/informalsystems/ibc-rs) repository, namely: the [__`ibc`__](https://github.com/informalsystems/ibc-rs/tree/master/modules) modules crate, [__`ibc-relayer`__](https://github.com/informalsystems/ibc-rs/tree/master/relayer) crate, [__`ibc-proto`__](https://github.com/informalsystems/ibc-rs/tree/master/proto) crate, and the [__`ibc-relayer-cli`__](https://github.com/informalsystems/ibc-rs/tree/master/relayer-cli) crate.
The last of these crates contains the `hermes` binary.

```shell
cargo build --release --bin hermes
```

If the build is successful, the `hermes` executable will be located in the following location:

```shell
./target/release/hermes
```

### Running for the first time

If you run the `hermes` without any additional parameters you should see the usage and help information:

```shell
./target/release/hermes
hermes 0.1.0
Informal Systems <hello@informal.systems>

USAGE:
    hermes <SUBCOMMAND>

SUBCOMMANDS:
    help       Get usage information
    keys       Manage keys in the relayer for each chain
    light      Basic functionality for managing the light clients
    start      Start the relayer
    channel    Channel functionality for managing channels
    query      Query state from chain
    tx         Create and send IBC transactions
    listen     Listen to and display IBC events emitted by a chain
    version    Display version information
```

### Creating an alias for the executable

It might be easier to create an alias for `hermes` so you can just run it by specifying the executable name instead of the whole path. In order to create an alias execute the following command:

```shell
alias hermes='cargo run --release --bin hermes --'
```

### Next Steps

Go to the [`Configuration`](./config.md) section to learn how to create a configuration file to be used by Hermes.

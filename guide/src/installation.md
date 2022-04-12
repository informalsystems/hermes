# Install the relayer

There are two main approaches for obtaining Hermes:

1. Installation:
   1. If you are running on a Unix machine (Linux/MacOS), then the simplest
      option is to [download the latest binary](#install-by-downloading).
   2. You can also install via [Cargo](#install-via-cargo).

2. Alternatively, [build Hermes directly from source](#build-from-source).


## Install by downloading

Simply head to the GitHub [Releases][releases] page and download the latest
version of Hermes binary matching your platform:
- MacOS: `hermes-v0.13.0-x86_64-apple-darwin.tar.gz` (or .zip),
- Linux: `hermes-v0.13.0-x86_64-unknown-linux-gnu.tar.gz` (or .zip).

The step-by-step instruction below should carry you through the whole process:

1. Make the directory where we'll place the binary:
   ```shell
   mkdir -p $HOME/.hermes/bin
   ```

2. Extract the binary archive:
   ```shell
   tar -C $HOME/.hermes/bin/ -vxzf $ARCHIVE_NAME
   ```

3. Update your path, by adding this line in your `.bashrc` or `.zshrc` shell
   configuration file:
   ```shell
   export PATH="$HOME/.hermes/bin:$PATH"
   ```

> NOTE: The binary may be initially prevented from running if you're
> on MacOS.
> See the ["Open Anyway" instructions from this support forum][developer-app]
> if that is the case.

You should now be able to run Hermes by invoking the `hermes` executable.

```shell
hermes version
```

```
hermes 0.13.0
```

## Install via Cargo

> NOTE: This approach assumes you have installed all
> the [pre-requisites](./pre_requisites.md) on your machine.

Hermes is packaged in the `ibc-relayer-cli` Rust crate.
To install the latest release of Hermes, run the following command in a terminal:

```shell
cargo install ibc-relayer-cli --bin hermes --locked
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
```

```
hermes 0.13.0
```

## Build from source

### Clone the repository

Open a terminal and clone the `ibc-rs` repository:

```shell
git clone https://github.com/informalsystems/ibc-rs.git
```

Change to the repository directory
```shell
cd ibc-rs
```

### Checkout the latest release

Go to the [ibc-rs releases](https://github.com/informalsystems/ibc-rs/releases) page to see what is the most recent release.

Then checkout the release, for example if the most recent release is `v0.13.0` then execute the command:

```shell
git checkout v0.13.0
```

### Building with `cargo build`

This command builds all the crates from the [__`ibc-rs`__](https://github.com/informalsystems/ibc-rs) repository, namely: the [__`ibc`__](https://github.com/informalsystems/ibc-rs/tree/master/modules) modules crate, [__`ibc-relayer`__](https://github.com/informalsystems/ibc-rs/tree/master/relayer) crate, [__`ibc-proto`__](https://github.com/informalsystems/ibc-rs/tree/master/proto) crate, and the [__`ibc-relayer-cli`__](https://github.com/informalsystems/ibc-rs/tree/master/relayer-cli) crate.
The last of these crates contains the `hermes` binary.

```shell
cargo build --release --bin hermes
```

<a name="telemetry-support"></a>

> By default, Hermes bundles a [telemetry service and server](./telemetry.md).
> To build Hermes without telemetry support, and get a smaller executable,
> supply the `--no-default-features flag` to `cargo build`:
>
> ```shell
> cargo build --release --no-default-features --bin hermes
> ```

If the build is successful, the `hermes` executable will be located in the following location:

```shell
./target/release/hermes
```

__Troubleshooting__:
In case the `cargo build` command above fails, as a first course of action we
recommend trying to run the same command with the additional `locked` flag:

```shell
cargo build --release --bin hermes --locked
```

### Running for the first time

If you run the `hermes` without any additional parameters you should see the usage and help information:

```shell
./target/release/hermes
```

```
hermes 0.13.0
Informal Systems <hello@informal.systems>

USAGE:
    hermes <SUBCOMMAND>

SUBCOMMANDS:
    help       Get usage information
    config     Validate Hermes configuration file
    keys       Manage keys in the relayer for each chain
    create     Create objects (client, connection, or channel) on chains
    update     Update objects (clients) on chains
    upgrade    Upgrade objects (clients) after chain upgrade
    start      Start the relayer
    query      Query objects from the chain
    tx         Create and send IBC transactions
    listen     Listen to and display IBC events emitted by a chain
    misbehaviour Listen to client update IBC events and handles misbehaviour
    version    Display version information
```

### Creating an alias for the executable

It might be easier to create an alias for `hermes` so you can just run it by specifying the executable name instead of the whole path. In order to create an alias execute the following command:

```shell
alias hermes='cargo run --release --bin hermes --'
```

## Shell auto-completions

The `completions` subcommand of Hermes can be used to output a completion script
for a choice of widely used command-line shells.
Refer to `hermes completions --help` for the list. Some shell-specific examples
of setting up auto-completion with this command are provided below; check your
shell configuration to decide on the suitable directory in which to install the script
and any further necessary modifications to the shell's startup files.

### Bash

```sh
hermes completions bash > ~/.local/share/bash-completion/completions/hermes
```

On a MacOS installation with Homebrew `bash-completion` formula installed, use 

```sh
hermes completions bash > $(brew --prefix)/etc/bash_completion.d/hermes.bash-completion
```

### Zsh

```sh
hermes completions zsh > ~/.zfunc/_hermes
```

To make the shell load the script on initialization, add the directory to `fpath`
in your `~/.zshrc` before `compinit`:

```
fpath+=~/.zfunc
```

## Next Steps

Go to the [`Configuration`](./config.md) section to learn how to create a configuration file to be used by Hermes.


[releases]: https://github.com/informalsystems/ibc-rs/releases
[developer-app]: https://support.apple.com/en-gb/HT202491

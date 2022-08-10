# Config

#### Show usage

To see the available sub-commands for the `config` command run:

```shell
hermes help config
```

The available sub-commands are the following:

```shell
USAGE:
    hermes config <SUBCOMMAND>

OPTIONS:
    -h, --help    Print help information

SUBCOMMANDS:
    auto        Automatically generate a relayer configuration file
    help        Print this message or the help of the given subcommand(s)
    validate    Validate the relayer configuration
```

### Automatically generate configuration
Use `config auto` to automatically generate a configuration file from the [chain-registry](https://github.com/cosmos/chain-registry).

> __WARNING__: Currently, gas parameters are set to default value and require to be set manually.

```
USAGE:
    hermes config auto --path <PATH> --chains <CHAIN_NAME_1 CHAIN_NAME_2...>... --keys <KEY_CHAIN_1 KEY_CHAIN_2...>...

OPTIONS:
    -h, --help    Print help information

REQUIRED:
        --chains <CHAIN_NAME_1 CHAIN_NAME_2...>...
            Names of the chains to include in the config. Every chain must be in the chain registry.

        --keys <KEY_CHAIN_1 KEY_CHAIN_2...>...
            Key names to include in the config. Must provide keys for every chain.

        --path <PATH>
            Path to the configuration file
DESCRIPTION:
    Automatically generate a configuration file by fetching data from the chain-registry. If a pair of chains exists in the _IBC folder of the chain-registry then a corresponding packet filter is added to the configuration
```

__Example__

Use `config auto` to generate a configuration file able to relay between `cosmoshub` and `osmosis`.
```
    hermes config auto --path $HOME/example_config.toml --chains cosmoshub osmosis --keys key_cosmoshub key_osmosis

    2022-08-10T16:03:05.282779Z  INFO ThreadId(01) using default configuration from '$HOME/.hermes/config.toml'
SUCCESS "Config file written successfully :$HOME/example_config.toml."
```
__WARNING__ : Do not forget to modify the gas settings before relaying !

### Validate configuration

Use `config validate` to perform a quick syntactic validation of
your configuration file.

```shell
USAGE:
    hermes config validate

DESCRIPTION:
    validate the relayer configuration
```

__Example__

Validate the default config file, the path inferred automatically to be
`$HOME/.hermes/config.toml`.

```shell
hermes config validate
```

```text
hermes config validate
Jul 12 16:31:07.017  INFO using default configuration from '$HOME/.hermes/config.toml'
SUCCESS: "validation passed successfully"
```

Validate a config file at an arbitrary location:

```shell
hermes --config ./config.toml config validate
```

This one fails validation because we mistakenly added two separate sections for
the same chain `ibc-1`:

```text
hermes --config ./config.toml config validate
error: hermes fatal error: config error: config file has duplicate entry for the chain 'ibc-1'
```

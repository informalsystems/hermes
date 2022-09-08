# Config

#### Show usage

To see the available sub-commands for the `config` command run:

```shell
hermes help config
```

The available sub-commands are the following:

```shell
{{#template ../../templates/help_templates/config.md}}
```

### Automatically generate configuration
Use `config auto` to automatically generate a configuration file from the [chain-registry](https://github.com/cosmos/chain-registry).

> __WARNING__: Currently, gas parameters are set to default value and require to be set manually.

```
{{#template ../../templates/help_templates/config/auto.md}}
```

__Example__

Use `config auto` to generate a configuration file able to relay between `cosmoshub` and `osmosis`. This command assumes the existence of a key file for `cosmoshub-4` and `osmosis-1` in `$HOME/.hermes/keys`.
```
    hermes config auto --output ~/example_config.toml --chains cosmoshub osmosis

2022-08-16T17:27:26.966233Z  INFO ThreadId(01) using default configuration from '~/.hermes/config.toml'
2022-08-16T17:27:27.800213Z  INFO ThreadId(01) cosmoshub-4: uses key "key_cosmoshub"
2022-08-16T17:27:27.841167Z  INFO ThreadId(01) osmosis-1: uses key "key_osmosis"
2022-08-16T17:27:27.841890Z  WARN ThreadId(01) Gas parameters are set to default values.
SUCCESS "Config file written successfully : ~/example_config.toml."
```

It is also possible to manually specify a key name for any chain.
```
    hermes config auto --output $HOME/example_config.toml --chains cosmoshub:random_key osmosis 

2022-08-16T17:29:56.902499Z  INFO ThreadId(01) using default configuration from '~/.hermes/config.toml'
2022-08-16T17:29:57.288874Z  INFO ThreadId(01) cosmoshub-4: uses key "random_key"
2022-08-16T17:29:57.289728Z  INFO ThreadId(01) osmosis-1: uses key "key_osmosis"
2022-08-16T17:29:57.290314Z  WARN ThreadId(01) Gas parameters are set to default values.
SUCCESS "Config file written successfully : ~/example_config.toml."
```

__WARNING__ : Do not forget to modify the gas settings before relaying !

### Validate configuration

Use `config validate` to perform a quick syntactic validation of
your configuration file.

```shell
{{#template ../../templates/help_templates/config/validate.md}}
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

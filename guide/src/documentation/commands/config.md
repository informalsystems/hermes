# Generating and Validating Config Files

#### Show usage

To see the available sub-commands for the `config` command run:

```shell
hermes help config
```

The available sub-commands are the following:

```shell
{{#include ../../templates/help_templates/config.md}}
```

### Automatically generate configuration files for specified chains 
Use `config auto` to automatically generate a configuration file from the [chain-registry](https://github.com/cosmos/chain-registry).

> __WARNING__: Currently, `default_gas` and `max_gas` parameters are set to default values; these should be manually reset. The `gas_price` parameter is set as the average gas price listed for the chain in the chain registry.

```
{{#include ../../templates/help_templates/config/auto.md}}
```

__Example__

Use `config auto` to generate a configuration file that is able to relay between `cosmoshub` and `osmosis`. This command assumes the existence of a key file for `cosmoshub-4` and `osmosis-1` in `$HOME/.hermes/keys`.
```
{{#template ../../templates/commands/hermes/config/auto_1.md PATH=~/example_config.toml CHAIN1_NAME:OPTIONAL_KEY_NAME=cosmoshub osmosis}}

2022-08-16T17:27:26.966233Z  INFO ThreadId(01) using default configuration from '~/.hermes/config.toml'
2022-08-16T17:27:27.800213Z  INFO ThreadId(01) cosmoshub-4: uses key "key_cosmoshub"
2022-08-16T17:27:27.841167Z  INFO ThreadId(01) osmosis-1: uses key "key_osmosis"
2022-08-16T17:27:27.841890Z  WARN ThreadId(01) Gas parameters are set to default values.
SUCCESS Config file written successfully at '~/example_config.toml'
```

It is also possible to manually specify a key name for any chain.
```
{{#template ../../templates/commands/hermes/config/auto_1.md PATH=~/example_config.toml CHAIN1_NAME:OPTIONAL_KEY_NAME=cosmoshub:random_key osmosis}}

2022-08-16T17:29:56.902499Z  INFO ThreadId(01) using default configuration from '~/.hermes/config.toml'
2022-08-16T17:29:57.288874Z  INFO ThreadId(01) cosmoshub-4: uses key "random_key"
2022-08-16T17:29:57.289728Z  INFO ThreadId(01) osmosis-1: uses key "key_osmosis"
2022-08-16T17:29:57.290314Z  WARN ThreadId(01) Gas parameters are set to default values.
SUCCESS "Config file written successfully : ~/example_config.toml."
```

__WARNING__ : Do not forget to modify the gas settings before relaying !

### Validate an existing configuration file

Use `config validate` to perform a quick syntactic validation of
your configuration file.

```shell
{{#include ../../templates/help_templates/config/validate.md}}
```

__Example__

Validate the default config file, the path inferred automatically to be
`$HOME/.hermes/config.toml`.

```shell
{{#template ../../templates/commands/hermes/config/validate_1.md}}
```
Which should output something similar to:
```text
Jul 12 16:31:07.017  INFO using default configuration from '$HOME/.hermes/config.toml'
SUCCESS: "validation passed successfully"
```

Validate a config file at an arbitrary location:

```shell
{{#template ../../templates/commands/hermes/config/validate_1.md GLOBALOPTIONS=  --config $CONFIGPATH}}
```

This one should fail validation because we mistakenly added two separate sections for the same chain `ibc-1`:

```text
error: hermes fatal error: config error: config file has duplicate entry for the chain 'ibc-1'
```

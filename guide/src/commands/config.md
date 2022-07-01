# Config


Use the `config validate` command to perform a quick syntactic validation of
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
Success: "validation passed successfully"
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

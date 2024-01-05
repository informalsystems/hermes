## Set Log Level

This command allows you to easily update the lowest log level displayed by Hermes.

```shell
{{#include ../../../templates/help_templates/logs/log-level.md}}
```

## Set Raw Filter

This command allows you to update the tracing directive used to filter the logs. Please use this command with caution as it requires a precise syntax.

```shell
{{#include ../../../templates/help_templates/logs/raw.md}}
```

## Reset

This command will restore the lowest log level displayed using the `log_level` defined in the `config.toml`.

```shell
{{#include ../../../templates/help_templates/logs/reset.md}}
```
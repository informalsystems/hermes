# Help command

The CLI comprises a special `help` command, which accepts as parameter other commands, and provides guidance on what is the correct way to invoke those commands.

> __NOTE__: This special `help` command is preferred as it will display the full help
> message.

For instance,

```shell
hermes help create
```

will provide details about all the valid invocations of the `create` CLI command.

```
{{#include ../../templates/help_templates/create.md}}
```

This can provide further specific guidance if we add additional parameters, e.g., 

```shell
hermes help create channel
```

```shell
{{#include ../../templates/help_templates/create/channel.md}}
```

Additionally, the `-h`/`--help` flags typical for CLI applications work on
all commands.

# Upgrading Clients
If IBC clients need to be upgraded after their reference chains went through an upgrade, the following CLIs may be used.

## Upgrade Client Command
Use the `upgrade client` command to upgrade a specific IBC client after a chain upgrade.

```shell
{{#include ../../../templates/help_templates/upgrade/client.md}}
```

## Upgrade Clients Command

Use the `upgrade clients` command to upgrade all IBC clients that target a specific (upgraded) chain.

```shell
{{#include ../../../templates/help_templates/upgrade/clients.md}}
```

__Example__

Here is [an example](./test.md) of a chain upgrade proposal submission and client upgrade.

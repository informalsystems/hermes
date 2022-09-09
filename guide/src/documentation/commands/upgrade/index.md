# Client Upgrade

## Client Upgrade Command

Use the `upgrade client` command to upgrade a client after a chain upgrade.

```shell
USAGE:
    hermes upgrade client --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID> --upgrade-height <REFERENCE_UPGRADE_HEIGHT>

DESCRIPTION:
    Upgrade an IBC client

REQUIRED:
        --client <CLIENT_ID>
            Identifier of the client to be upgraded

        --host-chain <HOST_CHAIN_ID>
            Identifier of the chain that hosts the client

        --upgrade-height <REFERENCE_UPGRADE_HEIGHT>
            The height at which the reference chain halts for the client upgrade
```

__Example__

Here is [an example](./test.md) of a chain upgrade proposal submission and client upgrade.

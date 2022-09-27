DESCRIPTION:
Upgrade an IBC client

USAGE:
    hermes upgrade client --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID> --upgrade-height <REFERENCE_UPGRADE_HEIGHT>

OPTIONS:
    -h, --help    Print help information

REQUIRED:
        --client <CLIENT_ID>
            Identifier of the client to be upgraded

        --host-chain <HOST_CHAIN_ID>
            Identifier of the chain that hosts the client

        --upgrade-height <REFERENCE_UPGRADE_HEIGHT>
            The height at which the reference chain halts for the client upgrade

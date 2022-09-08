DESCRIPTION:
Upgrade all IBC clients that target a specific chain

USAGE:
    hermes upgrade clients [OPTIONS] --reference-chain <REFERENCE_CHAIN_ID> --upgrade-height <REFERENCE_UPGRADE_HEIGHT>

OPTIONS:
    -h, --help                          Print help information
        --host-chain <HOST_CHAIN_ID>    Identifier of the chain hosting the clients to be upgraded

REQUIRED:
        --reference-chain <REFERENCE_CHAIN_ID>
            Identifier of the chain that underwent an upgrade; all clients targeting this chain will
            be upgraded

        --upgrade-height <REFERENCE_UPGRADE_HEIGHT>
            The height at which the reference chain halts for the client upgrade

DESCRIPTION:
Update an IBC client

USAGE:
    hermes update client [OPTIONS] --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>

OPTIONS:
    -h, --help
            Print help information

        --height <REFERENCE_HEIGHT>
            The target height of the client update. Leave unspecified for latest height.

        --trusted-height <REFERENCE_TRUSTED_HEIGHT>
            The trusted height of the client update. Leave unspecified for latest height.

REQUIRED:
        --client <CLIENT_ID>            Identifier of the chain targeted by the client
        --host-chain <HOST_CHAIN_ID>    Identifier of the chain that hosts the client

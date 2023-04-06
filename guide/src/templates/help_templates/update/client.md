DESCRIPTION:
Update an IBC client

USAGE:
    hermes update client [OPTIONS] --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>

OPTIONS:
        --archive-address <ARCHIVE_ADDRESS>
            The archive node address used to update client. Requires --halted-height if used.
            [aliases: archive-addr]

    -h, --help
            Print help information

        --halted-height <HALTED_HEIGHT>
            The height that the chain halted. Requires --archive-address if used.

        --height <REFERENCE_HEIGHT>
            The target height of the client update. Leave unspecified for latest height.

        --trusted-height <REFERENCE_TRUSTED_HEIGHT>
            The trusted height of the client update. Leave unspecified for latest height.

REQUIRED:
        --client <CLIENT_ID>            Identifier of the client to update
        --host-chain <HOST_CHAIN_ID>    Identifier of the chain that hosts the client

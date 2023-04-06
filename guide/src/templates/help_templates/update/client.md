DESCRIPTION:
Update an IBC client

USAGE:
    hermes update client [OPTIONS] --host-chain <HOST_CHAIN_ID> --client <CLIENT_ID>

OPTIONS:
        --archive-address <ARCHIVE_ADDRESS>
            The RPC address of the archive node to use to fetch headers from before the restart.
            Requires --restart-height if used. [aliases: archive-addr]

    -h, --help
            Print help information

        --height <REFERENCE_HEIGHT>
            The target height of the client update. Leave unspecified for latest height.

        --restart-height <RESTART_HEIGHT>
            The height that the chain underwent a genesis restart at. Requires --archive-address if
            used.

        --trusted-height <REFERENCE_TRUSTED_HEIGHT>
            The trusted height of the client update. Leave unspecified for latest height.

REQUIRED:
        --client <CLIENT_ID>            Identifier of the client to update
        --host-chain <HOST_CHAIN_ID>    Identifier of the chain that hosts the client

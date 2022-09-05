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
USAGE:
    hermes create <SUBCOMMAND>

DESCRIPTION:
    Create objects (client, connection, or channel) on chains

SUBCOMMANDS:
    channel       Create a new channel between two chains
    client        Create a new IBC client
    connection    Create a new connection between two chains
    help          Print this message or the help of the given subcommand(s)
```

This can provide further specific guidance if we add additional parameters, e.g., 

```shell
hermes help create channel
```

```shell
USAGE:
    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --a-connection <A_CONNECTION_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID>

    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --b-chain <B_CHAIN_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID> --new-client-connection

DESCRIPTION:
    Create a new channel between two chains.

    Can create a new channel using a pre-existing connection or alternatively, create a new client and a
    new connection underlying the new channel if a pre-existing connection is not provided.

OPTIONS:
        --channel-version <VERSION>
            The version for the new channel

            [aliases: chan-version]

        --new-client-connection
            Indicates that a new client and connection will be created underlying the new channel

            [aliases: new-client-conn]

        --order <ORDER>
            The channel ordering, valid options 'unordered' (default) and 'ordered'

            [default: ORDER_UNORDERED]

        --yes
            Skip new_client_connection confirmation

FLAGS:
        --a-chain <A_CHAIN_ID>
            Identifier of the side `a` chain for the new channel

        --a-connection <A_CONNECTION_ID>
            Identifier of the connection on chain `a` to use in creating the new channel

            [aliases: a-conn]

        --a-port <A_PORT_ID>
            Identifier of the side `a` port for the new channel

        --b-chain <B_CHAIN_ID>
            Identifier of the side `b` chain for the new channel

        --b-port <B_PORT_ID>
            Identifier of the side `b` port for the new channel
```

Additionally, the `-h`/`--help` flags typical for CLI applications work on
all commands.

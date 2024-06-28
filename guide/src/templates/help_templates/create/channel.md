DESCRIPTION:
Create a new channel between two chains.

Can create a new channel using a pre-existing connection or alternatively, create a new client and a
new connection underlying the new channel if a pre-existing connection is not provided.

USAGE:
    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --a-connection <A_CONNECTION_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID>

    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --b-chain <B_CHAIN_ID> --a-port <A_PORT_ID> --b-port <B_PORT_ID> --new-client-connection

    hermes create channel [OPTIONS] --a-chain <A_CHAIN_ID> --a-connection <A_CONNECTION_ID> --connection-hops <CONNECTION_HOP_IDS> --a-port <A_PORT_ID> --b-port <B_PORT_ID>

    NOTE: The `--new-client-connection` option does not support connection hops. To open a multi-hop channel, please provide existing connections or initialize them manually before invoking this command.

OPTIONS:
        --channel-version <VERSION>
            The version for the new channel
            
            [aliases: chan-version]

    -h, --help
            Print help information

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

        --connection-hops <CONNECTION_IDS>
            A list of identifiers of the intermediate connections between side `a` and side `b` for
            a multi-hop channel, separated by slashes, e.g, 'connection-1/connection-0' (optional).
            
            [aliases: conn-hops]

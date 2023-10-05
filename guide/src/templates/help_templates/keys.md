DESCRIPTION:
Manage keys in the relayer for each chain

USAGE:
    hermes keys <SUBCOMMAND>

OPTIONS:
    -h, --help    Print help information

SUBCOMMANDS:
    add        Add a key to a chain from its keyring file or restore a key using its mnemonic
    balance    Query balance for a key from a configured chain. If no key is given, the key is
                   retrieved from the configuration file
    delete     Delete key(s) from a configured chain
    help       Print this message or the help of the given subcommand(s)
    list       List keys configured for a chain

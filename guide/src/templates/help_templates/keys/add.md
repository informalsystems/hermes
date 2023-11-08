DESCRIPTION:
Add a key to a chain from its keyring file or restore a key using its mnemonic

USAGE:
    Add a key from a Comet keyring file:
        hermes keys add [OPTIONS] --chain <CHAIN_ID> --key-file <KEY_FILE>
    
    Add a key from a file containing its mnemonic:
        hermes keys add [OPTIONS] --chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE>
    
    On *nix platforms, both flags also accept `/dev/stdin` as a value, which will read the key or the mnemonic from stdin.

OPTIONS:
    -h, --help                   Print help information
        --hd-path <HD_PATH>      Derivation path for this key [default: m/44'/118'/0'/0/0]
        --key-name <KEY_NAME>    Name of the key (defaults to the `key_name` defined in the config)
        --overwrite              Overwrite the key if there is already one with the same key name

FLAGS:
        --chain <CHAIN_ID>
            Identifier of the chain

        --key-file <KEY_FILE>
            Path to the key file, or /dev/stdin to read the content from stdin

        --mnemonic-file <MNEMONIC_FILE>
            Path to file containing the mnemonic to restore the key from, or /dev/stdin to read the
            mnemonic from stdin

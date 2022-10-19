DESCRIPTION:
Query balance for a key from a configured chain. If no key is given, the key is retrieved from the
configuration file

USAGE:
    hermes keys balance [OPTIONS] --chain <CHAIN_ID>

OPTIONS:
        --all                    (optional) query the balance for all denom. This flag overwrites
                                 the `--denom` flag (defaults to false)
        --denom <DENOM>          (optional) query the balance for the given denom (defaults to the
                                 `denom` defined in the config for the gas price)
    -h, --help                   Print help information
        --key-name <KEY_NAME>    (optional) name of the key (defaults to the `key_name` defined in
                                 the config)

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain

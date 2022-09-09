DESCRIPTION:
Automatically generate a configuration file by fetching data from the chain-registry. If a pair of
chains exists in the _IBC folder of the chain-registry then a corresponding packet filter is added
to the configuration

USAGE:
    hermes config auto [OPTIONS] --output <PATH> --chains <CHAIN_NAME:OPTIONAL_KEY_NAME>

OPTIONS:
        --commit <COMMIT_HASH>    Commit hash from which the chain configs will be generated. If
                                  it's not set, the latest commit will be used.
    -h, --help                    Print help information

REQUIRED:
        --chains <CHAIN_NAME:OPTIONAL_KEY_NAME>...
            Names of the chains to include in the config. Every chain must be in the chain registry.

        --output <PATH>
            Path to the configuration file

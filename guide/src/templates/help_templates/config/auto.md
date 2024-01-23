DESCRIPTION:
Automatically generate a config.toml for the specified chain(s)

USAGE:
    hermes config auto [OPTIONS] --output <PATH> --chain <CHAIN1_NAME:OPTIONAL_KEY_NAME> --chain <CHAIN2_NAME:OPTIONAL_KEY_NAME>

OPTIONS:
        --commit <COMMIT_HASH>    Commit hash from which the chain configs will be generated. If
                                  it's not set, the latest commit will be used.
    -h, --help                    Print help information

REQUIRED:
        --chains <CHAIN_NAME:OPTIONAL_KEY_NAME>...
            Names of the chains to include in the configuration, together with an optional key name.
            Either repeat this argument for every chain or pass a space-separated list of chains.
            Every chain must be found in the chain registry.

        --output <PATH>
            Path to the configuration file

DESCRIPTION:
Listen to block events and handles evidence

USAGE:
    hermes evidence [OPTIONS] --chain <CHAIN_ID>

OPTIONS:
        --check-past-blocks <NUM_BLOCKS>
            Check the last NUM_BLOCKS blocks for misbehaviour (default: 100) [default: 100]

    -h, --help
            Print help information

        --key-name <KEY_NAME>
            Use the given signing key name for sending the misbehaviour evidence detected (default:
            `key_name` config)

REQUIRED:
        --chain <CHAIN_ID>    Identifier of the chain where blocks are monitored for misbehaviour

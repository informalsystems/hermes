DESCRIPTION:
Informal Systems <hello@informal.systems>
  Hermes is an IBC Relayer written in Rust

USAGE:
    hermes [OPTIONS] [SUBCOMMAND]

OPTIONS:
        --config <CONFIG>    Path to configuration file
        --debug <DEBUG>      Enable debug output for the given section(s), comma separated, can be
                             repeated. [possible values: rpc, profiling, profiling-json]
    -h, --help               Print help information
        --json               Enable JSON output
    -V, --version            Print version information

SUBCOMMANDS:
    clear           Clear objects, such as outstanding packets on a channel
    config          Generate a new Hermes configuration file or validate an existing one
    create          Create objects (client, connection, or channel) on chains
    evidence        Listen to block events and handles evidence
    fee             Interact with the fee middleware
    health-check    Performs a health check of all chains in the config
    help            Print this message or the help of the given subcommand(s)
    keys            Manage keys in the relayer for each chain
    listen          Listen to and display IBC events emitted by a chain
    logs            Update tracing log directives
    misbehaviour    Listen to client update IBC events and handle misbehaviour
    query           Query objects from the chain
    start           Start the relayer in multi-chain mode
    tx              Create and send IBC transactions
    update          Update objects (clients) on chains
    upgrade         Upgrade objects (clients) after chain upgrade
    completions     Generate auto-complete scripts for different shells

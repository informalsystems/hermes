DESCRIPTION:
Validate Hermes configuration file

USAGE:
    hermes config <SUBCOMMAND>

OPTIONS:
    -h, --help    Print help information

SUBCOMMANDS:
    auto        Automatically generate a configuration file by fetching data from the
                    chain-registry. If a pair of chains exists in the _IBC folder of the
                    chain-registry then a corresponding packet filter is added to the configuration
    help        Print this message or the help of the given subcommand(s)
    validate    Validate the relayer configuration

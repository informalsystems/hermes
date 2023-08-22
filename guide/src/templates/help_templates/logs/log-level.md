DESCRIPTION:
Subcommand used to easily update the lowest log level displayed

USAGE:
    hermes logs log-level [OPTIONS] --log-level <LOG_LEVEL>

OPTIONS:
    -h, --help                     Print help information
        --log-level <LOG_LEVEL>    The new lowest log level which will be displayed. Possible values
                                   are `trace`, `debug`, `info`, `warn` or `error`

FLAGS:
        --log-filter <LOG_FILTER>    The target of the log level to update, if left empty all the
                                     targets will be updated. Example `ibc` or `tendermint_rpc`

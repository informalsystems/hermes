use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;
use tracing::Level;

use crate::prelude::app_config;
use crate::tracing_handle::send_command;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct SetLogLevelCmd {
    #[clap(
        long = "log-level",
        required = true,
        value_name = "LOG_LEVEL",
        help = "The new lowest log level which will be displayed. Possible values are `trace`, `debug`, `info`, `warn` or `error`"
    )]
    log_level: Level,

    #[clap(
        long = "log-filter",
        help_heading = "FLAGS",
        value_name = "LOG_FILTER",
        help = "The target of the log level to update, if left empty all the targets will be updated. Example `ibc` or `tendermint_rpc`"
    )]
    log_filter: Option<String>,
}

impl Runnable for SetLogLevelCmd {
    fn run(&self) {
        let config = app_config();

        let port = config.tracing_server.port;

        let str_log = self.log_level.clone().to_string();
        if let Some(log_filter) = self.log_filter.clone() {
            let log_cmd = format!("{log_filter}={str_log}");
            send_command(log_cmd, port)
        } else {
            send_command(str_log, port)
        }
    }
}

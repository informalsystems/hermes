use std::str::FromStr;

use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;
use tracing::error;

use crate::error::Error;
use crate::prelude::app_config;
use crate::tracing_handle::send_command;

#[derive(Clone, Debug, Eq, PartialEq)]
enum LogLevelCommands {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

impl TryInto<String> for LogLevelCommands {
    type Error = Error;

    fn try_into(self) -> Result<String, Error> {
        match self {
            LogLevelCommands::Trace => Ok("trace".to_owned()),
            LogLevelCommands::Debug => Ok("debug".to_owned()),
            LogLevelCommands::Info => Ok("info".to_owned()),
            LogLevelCommands::Warn => Ok("warn".to_owned()),
            LogLevelCommands::Error => Ok("error".to_owned()),
        }
    }
}

impl FromStr for LogLevelCommands {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "trace" => Ok(LogLevelCommands::Trace),
            "debug" => Ok(LogLevelCommands::Debug),
            "info" => Ok(LogLevelCommands::Info),
            "warn" => Ok(LogLevelCommands::Warn),
            "error" => Ok(LogLevelCommands::Error),
            cmd => Err(Error::unknown_log_level(cmd.to_owned())),
        }
    }
}

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct LogLevelCmd {
    #[clap(
        long = "log-level",
        required = true,
        value_name = "LOG_LEVEL",
        help = "The new lowest log level which will be displayed. Possible values are `trace`, `debug`, `info`, `warn` or `error`"
    )]
    log_level: LogLevelCommands,

    #[clap(
        long = "log-filter",
        help_heading = "FLAGS",
        value_name = "LOG_FILTER",
        help = "The target of the log level to update, if left empty all the targets will be updated. Example `ibc` or `tendermint_rpc`"
    )]
    log_filter: Option<String>,
}

impl Runnable for LogLevelCmd {
    fn run(&self) {
        let config = app_config();

        let port = config.tracing_server.port;

        let log_cmd: Result<String, Error> = self.log_level.clone().try_into();
        match log_cmd {
            Ok(cmd) => {
                if let Some(log_filter) = self.log_filter.clone() {
                    let log_cmd = format!("{log_filter}={cmd}");
                    send_command(log_cmd, port)
                } else {
                    send_command(cmd, port)
                }
            }
            Err(e) => error!("error: {e}"),
        }
    }
}

use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};

pub mod log_level;
pub mod raw;
pub mod reset;

/// `logs` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum LogsCmd {
    /// Subcommand used to easily update the lowest log level displayed
    SetLogLevel(log_level::SetLogLevelCmd),

    /// Subcommand used to send a raw filter directive for logs displayed
    SetRawFilter(raw::SetRawFilterCmd),

    /// Subcommand to restore the log level by using the configuration defined in the config.toml file
    Reset(reset::ResetCmd),
}

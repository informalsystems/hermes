use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;

pub mod log_level;
pub mod raw;
pub mod reset;

/// `logs` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum LogsCmd {
    /// Subcommand used to easily update the lowest log level displayed
    LogLevel(log_level::LogLevelCmd),

    /// Subcommand used to send a raw directive for log display
    Raw(raw::RawCmd),

    /// Subcommand to restore the log level by using the configuration defined in the config.toml file
    Reset(reset::ResetCmd),
}

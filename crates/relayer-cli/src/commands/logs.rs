use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;

pub mod log_level;
pub mod raw;
pub mod reset;

/// `logs` subcommand
#[derive(Command, Debug, Parser, Runnable)]
pub enum LogsCmd {
    LogLevel(log_level::LogLevelCmd),

    Raw(raw::RawCmd),

    Reset(reset::ResetCmd),
}

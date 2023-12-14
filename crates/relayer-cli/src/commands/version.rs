//! `version` subcommand

use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};

use super::CliCmd;

/// `version` subcommand
///
/// This subcommand is implemented for backward compatibility reasons.
/// Its behavior should be the same as that of the `--version` flag which
/// is handled internally by clap.
#[derive(Command, Debug, Default, Parser)]
#[clap(hide = true)]
pub struct VersionCmd {}

impl Runnable for VersionCmd {
    /// Print version message
    fn run(&self) {
        println!("{} {}", CliCmd::name(), clap::crate_version!());
    }
}

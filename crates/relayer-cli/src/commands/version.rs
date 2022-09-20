//! `version` subcommand

use super::CliCmd;
use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

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

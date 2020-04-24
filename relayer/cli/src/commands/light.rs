//! `light` subcommand

use abscissa_core::{Command, Options, Runnable};

mod init;

/// `light` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum LightCmd {
    /// The `light init` subcommand
    #[options(help = "initiate a light client for a given chain")]
    Init(init::InitCmd),
}

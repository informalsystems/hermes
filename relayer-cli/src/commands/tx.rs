//! `tx` subcommand

use abscissa_core::{Command, Options, Runnable, Help};

mod raw;

/// `tx` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum TxCmd {
    /// The `help` subcommand
    #[options(help = "get usage information")]
    Help(Help<Self>),

    /// The `tx raw` subcommand
    #[options(help = "tx raw")]
    Raw(TxRawCmds),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum TxRawCmds {
    /// The `tx raw conninit` subcommand
    #[options(help = "tx raw conninit")]
    Handler(raw::TxRawConnInitCmd),
}
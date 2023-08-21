use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;

use crate::tracing_handle::send_command;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct RawCmd {
    #[clap(long = "log-level", help = "tmp")]
    cmd: String,
}

impl Runnable for RawCmd {
    fn run(&self) {
        send_command(self.cmd.clone());
    }
}

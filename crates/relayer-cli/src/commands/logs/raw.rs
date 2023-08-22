use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;

use crate::prelude::app_config;
use crate::tracing_handle::send_command;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct RawCmd {
    #[clap(
        long = "raw-cmd",
        required = true,
        value_name = "RAW_CMD",
        help = "Raw command used as new tracing directive. Use with caution"
    )]
    raw_cmd: String,
}

impl Runnable for RawCmd {
    fn run(&self) {
        let config = app_config();

        let port = config.tracing_server.port;

        send_command(self.raw_cmd.clone(), port);
    }
}

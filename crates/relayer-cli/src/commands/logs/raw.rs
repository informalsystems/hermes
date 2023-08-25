use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;

use crate::prelude::app_config;
use crate::tracing_handle::send_command;

// TODO `hermes set-raw-filter`
#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct SetRawFilterCmd {
    #[clap(
        long = "raw-filter",
        required = true,
        value_name = "RAW_FILTER",
        help = "Raw filter used as new tracing directive. Use with caution"
    )]
    raw_filter: String,
}

impl Runnable for SetRawFilterCmd {
    fn run(&self) {
        let config = app_config();

        let port = config.tracing_server.port;

        send_command(self.raw_filter.clone(), port);
    }
}

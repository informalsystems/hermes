use abscissa_core::clap::Parser;
use abscissa_core::Command;
use abscissa_core::Runnable;

use crate::components::default_directive;
use crate::prelude::*;
use crate::tracing_handle::send_command;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct ResetCmd {}

impl Runnable for ResetCmd {
    fn run(&self) {
        let config = app_config();

        let port = config.tracing_server.port;

        let directive = default_directive(config.global.log_level);

        send_command(directive, port);
    }
}

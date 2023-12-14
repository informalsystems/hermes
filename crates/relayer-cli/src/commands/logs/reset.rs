use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};

use crate::{
    components::default_directive,
    prelude::*,
    tracing_handle::send_command,
};

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct ResetCmd {}

impl Runnable for ResetCmd {
    fn run(&self) {
        let config = app_config();

        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        let port = config.tracing_server.port;
        let directive = default_directive(config.global.log_level);

        rt.block_on(run(&directive, port));
    }
}

async fn run(directive: &str, port: u16) {
    info!("Resetting log filter to: {directive}");
    let result = send_command(directive, port).await;

    match result {
        Ok(_) => info!("Successfully reset log filter"),
        Err(e) => error!("Failed to reset log filter: {e}"),
    }
}

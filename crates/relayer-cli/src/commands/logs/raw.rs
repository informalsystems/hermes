use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};
use tracing::{
    error,
    info,
};

use crate::{
    prelude::app_config,
    tracing_handle::send_command,
};

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

        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        let port = config.tracing_server.port;

        rt.block_on(run(&self.raw_filter, port));
    }
}

async fn run(raw_filter: &str, port: u16) {
    info!("Setting raw log filter to: {raw_filter}");
    let result = send_command(raw_filter, port).await;

    match result {
        Ok(_) => info!("Successfully set raw filter"),
        Err(e) => error!("Failed to set raw filter: {e}"),
    }
}

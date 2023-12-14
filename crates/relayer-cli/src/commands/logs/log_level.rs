use abscissa_core::{
    clap::Parser,
    Command,
    Runnable,
};
use tracing::{
    info,
    Level,
};

use crate::{
    prelude::app_config,
    tracing_handle::send_command,
};

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct SetLogLevelCmd {
    #[clap(
        long = "log-level",
        required = true,
        value_name = "LOG_LEVEL",
        help = "The new lowest log level which will be displayed. Possible values are `trace`, `debug`, `info`, `warn` or `error`"
    )]
    log_level: Level,

    #[clap(
        long = "log-filter",
        help_heading = "FLAGS",
        value_name = "LOG_FILTER",
        help = "The target of the log level to update, if left empty all the targets will be updated. Example `ibc` or `tendermint_rpc`"
    )]
    log_filter: Option<String>,
}

impl Runnable for SetLogLevelCmd {
    fn run(&self) {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        rt.block_on(run(&self.log_level, self.log_filter.as_ref()));
    }
}

async fn run(log_level: &Level, log_filter: Option<&String>) {
    let config = app_config();

    let port = config.tracing_server.port;

    let str_log = log_level.to_string();

    let result = if let Some(log_filter) = log_filter {
        let log_cmd = format!("{log_filter}={str_log}");
        info!("Setting log level to: {log_cmd}");
        send_command(&log_cmd, port).await
    } else {
        info!("Setting log level to: {str_log}");
        send_command(&str_log, port).await
    };

    match result {
        Ok(msg) => info!("{msg}"),
        Err(e) => info!("Failed to set log level: {e}"),
    }
}

use std::ops::Deref;

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use crate::{prelude::*, tasks::event_listener};

#[derive(Command, Debug, Options)]
pub struct ListenCmd {}

impl ListenCmd {
    async fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();

        debug!("launching 'listen' command");
        event_listener::start(&config, false).await
    }
}

impl Runnable for ListenCmd {
    fn run(&self) {
        let rt = tokio::runtime::Runtime::new().unwrap();

        rt.block_on(async move {
            self.cmd()
                .await
                .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e));
        });
    }
}

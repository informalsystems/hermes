use std::ops::Deref;

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use crate::{application::APPLICATION, prelude::*, tasks::event_listener};

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
        abscissa_tokio::run(&APPLICATION, async move {
            self.cmd()
                .await
                .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e));
        })
        .unwrap();
    }
}

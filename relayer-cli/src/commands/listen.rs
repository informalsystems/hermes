use std::{ops::Deref, sync::Arc};

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use crate::{prelude::*, tasks::event_listener};

#[derive(Command, Debug, Options)]
pub struct ListenCmd {}

impl ListenCmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();

        let rt = tokio::runtime::Runtime::new().unwrap();

        debug!("launching 'listen' command");
        event_listener::start(Arc::new(rt), &config, false)
    }
}

impl Runnable for ListenCmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e));
    }
}

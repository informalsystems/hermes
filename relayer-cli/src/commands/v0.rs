use crate::prelude::*;

use abscissa_core::{
    application::fatal_error, error::BoxError, tracing::debug, Command, Options, Runnable,
};

use std::ops::Deref;

use crate::config::Config;

#[derive(Command, Debug, Options)]
pub struct V0Cmd {}

impl V0Cmd {
    fn cmd(&self) -> Result<(), BoxError> {
        let config = app_config().clone();
        debug!("launching 'v0' command");
        v0_task(config)
    }
}

impl Runnable for V0Cmd {
    fn run(&self) {
        self.cmd()
            .unwrap_or_else(|e| fatal_error(app_reader().deref(), &*e))
    }
}

pub fn v0_task(config: Config) -> Result<(), BoxError> {
    todo!()
}

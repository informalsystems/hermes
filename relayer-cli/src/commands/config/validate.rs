use abscissa_core::{Command, Options, Runnable};

use crate::conclude::Output;
use crate::config;
use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct ValidateCmd {}

impl Runnable for ValidateCmd {
    /// Validate the loaded configuration.
    fn run(&self) {
        let config = app_config();
        trace!("loaded configuration: {:#?}", *config);

        // No need to output the underlying error, this is done already when the application boots.
        // See `application::CliApp::after_config`.
        match config::validate_config(&config) {
            Ok(_) => Output::success("configuration is valid").exit(),
            Err(_) => Output::error("configuration is invalid").exit(),
        }
    }
}

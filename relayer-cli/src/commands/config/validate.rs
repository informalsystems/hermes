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

        match config::validate_config(&config) {
            Ok(_) => Output::success("validation passed successfully").exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

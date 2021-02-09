use abscissa_core::{Command, Options, Runnable};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Command, Debug, Options)]
pub struct ValidateCmd {}

impl Runnable for ValidateCmd {
    /// Validate the loaded configuration.
    fn run(&self) {
        let config = app_config();
        info!("Loaded configuration: {:?}", *config);

        // TODO: Validate configuration

        Output::with_success().exit();
    }
}

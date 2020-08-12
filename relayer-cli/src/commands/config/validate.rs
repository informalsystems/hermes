use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};

#[derive(Command, Debug, Options)]
pub struct ValidateCmd {}

impl Runnable for ValidateCmd {
    /// Validate the loaded configuration.
    fn run(&self) {
        let config = app_config();
        status_ok!("Loaded configuration:", "{:#?}", *config);

        // TODO: Validate configuration
    }
}

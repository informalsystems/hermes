use std::fs;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use crate::conclude::Output;
use crate::config;

use ibc::core::ics24_host::identifier::ChainId;

use crate::prelude::*;

/// In order to validate the configuration file the command will check that the file exists,
/// that it is readable and not empty. It will then check the validity of the fields inside
/// the file.
#[derive(Clone, Command, Debug, Parser, PartialEq)]
pub struct AutomatedCmd {
    #[clap(
        long = "chains",
        required = true,
        multiple = true,
        value_name = "CHAIN_ID1 CHAIN_ID2...",
        help_heading = "REQUIRED",
        help = "Identifier of the chain to query"
    )]
    chain_ids: Vec<ChainId>,
}

impl Runnable for AutomatedCmd {
    /// Validate the loaded configuration.
    fn run(&self) {
        let config = app_config();
        trace!("loaded configuration: {:#?}", *config);

        self.chain_ids.iter().for_each(|chain_id| {
            println!("{}", chain_id);
        });

        // Verify that the configuration file has been found.
        match config::config_path() {
            Some(p) => {
                // If there is a configuration file, verify that it is readable and not empty.
                match fs::read_to_string(p.clone()) {
                    Ok(content) => {
                        if content.is_empty() {
                            Output::error("the configuration file is empty").exit();
                        }
                    }
                    Err(e) => Output::error(format!(
                        "error reading the configuration file {:?}: {}",
                        p, e
                    ))
                    .exit(),
                }
            }
            None => Output::error("no configuration file found").exit(),
        }

        // No need to output the underlying error, this is done already when the application boots.
        // See `application::CliApp::after_config`.
        match config::validate_config(&config) {
            Ok(_) => Output::success("configuration is valid").exit(),
            Err(_) => Output::error("configuration is invalid").exit(),
        }
    }
}

use abscissa_core::{Command, Options, Runnable};

use ibc_relayer::supervisor::Supervisor;
use ibc_relayer_rest::{config::Config as RESTConfig, server as RESTServer};

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {}

impl Runnable for StartMultiCmd {
    fn run(&self) {
        let config = app_config();
        let rest_config = RESTConfig {
            connection: config.global.rest_addr.clone(),
        };
        let (_, rest_receiver) = RESTServer::spawn(rest_config);
        let supervisor =
            Supervisor::spawn(config.clone(), rest_receiver).expect("failed to spawn supervisor");
        match supervisor.run() {
            Ok(()) => Output::success_msg("done").exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

use std::collections::HashMap;

use abscissa_core::{config, Command, Options, Runnable};

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{chain::handle::ChainHandle, supervisor::Supervisor};

use crate::conclude::Output;
use crate::prelude::*;
use crate::{application::CliApp, commands::cli_utils::ChainHandlePair};

use super::cli_utils::spawn_chain_runtime;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {
    #[options(free, help = "identifier of chain A")]
    chain_a: Option<ChainId>,

    #[options(free, help = "identifier of chain B")]
    chain_b: Option<ChainId>,
}

enum Opts<'a> {
    AllConnections,
    Specified {
        chain_a: &'a ChainId,
        chain_b: &'a ChainId,
    },
}

impl StartMultiCmd {
    fn validate_options(&self) -> Result<Opts<'_>, BoxError> {
        match (&self.chain_a, &self.chain_b) {
            (Some(chain_a), Some(chain_b)) => Ok(Opts::Specified { chain_a, chain_b }),
            (None, None) => Ok(Opts::AllConnections),
            _ => Err("invalid options: please specify both chain identifiers \
                      or none at all to use the connections defined in the configuration"
                .into()),
        }
    }

    fn cmd(&self) -> Result<Output, BoxError> {
        let options = self.validate_options()?;
        let config = app_config();

        match options {
            Opts::Specified { chain_a, chain_b } => start_specified(&config, chain_a, chain_b),
            Opts::AllConnections => start_all_connections(&config),
        }
    }
}

impl Runnable for StartMultiCmd {
    fn run(&self) {
        match self.cmd() {
            Ok(output) => output.exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

fn start_specified(
    config: &config::Reader<CliApp>,
    chain_a: &ChainId,
    chain_b: &ChainId,
) -> Result<Output, BoxError> {
    info!("spawning supervisor for chains {} and {}", chain_a, chain_b);

    let chains = ChainHandlePair::spawn(config, chain_a, chain_b)?;
    let supervisor = Supervisor::spawn(chains.src, chains.dst)?;
    supervisor.run()?;

    Ok(Output::success("ok"))
}

fn start_all_connections(config: &config::Reader<CliApp>) -> Result<Output, BoxError> {
    let connections = config
        .connections
        .as_ref()
        .filter(|conns| !conns.is_empty())
        .ok_or("no connections configured")?;

    let mut handles = HashMap::new();
    let mut get_handle = |id: &ChainId| -> Result<Box<dyn ChainHandle>, BoxError> {
        if !handles.contains_key(id) {
            let handle = spawn_chain_runtime(Default::default(), config, id)?;
            handles.insert(id.clone(), handle);
        }

        let handle = handles.get(id).unwrap();
        Ok(handle.clone())
    };

    for conn in connections {
        info!(
            "spawning supervisor for chains {} and {}",
            conn.a_chain, conn.b_chain
        );

        let chain_a = get_handle(&conn.a_chain)?;
        let chain_b = get_handle(&conn.b_chain)?;

        std::thread::spawn(|| {
            let supervisor = Supervisor::spawn(chain_a, chain_b)?;
            supervisor.run()
        });
    }

    Ok(Output::success("ok"))
}

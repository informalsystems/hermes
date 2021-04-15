use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{config::Config, supervisor::Supervisor};

use crate::conclude::Output;
use crate::prelude::*;
use crate::registry::Registry;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {
    #[options(free, help = "identifier of chain A")]
    chain_a: Option<ChainId>,

    #[options(free, help = "identifier of chain B")]
    chain_b: Option<ChainId>,
}

enum Opts<'a> {
    AllConnections,
    Specified(&'a ChainId, &'a ChainId),
}

impl StartMultiCmd {
    fn validate_options(&self) -> Result<Opts<'_>, BoxError> {
        match (&self.chain_a, &self.chain_b) {
            (Some(chain_a), Some(chain_b)) => Ok(Opts::Specified(chain_a, chain_b)),
            (None, None) => Ok(Opts::AllConnections),
            _ => Err("invalid options: please specify both chain identifiers \
                      or none at all to use the connections defined in the configuration"
                .into()),
        }
    }

    fn cmd(&self) -> Result<Output, BoxError> {
        let options = self.validate_options()?;
        let config = &*app_config();

        match options {
            Opts::Specified(chain_a, chain_b) => start_specified(config, chain_a, chain_b),
            Opts::AllConnections => start_all_connections(config),
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
    config: &Config,
    chain_a: &ChainId,
    chain_b: &ChainId,
) -> Result<Output, BoxError> {
    info!("spawning supervisor for chains {} and {}", chain_a, chain_b);

    let mut registry = Registry::new(&config);
    let chain_a = registry.get_or_spawn(chain_a)?;
    let chain_b = registry.get_or_spawn(chain_b)?;

    let supervisor = Supervisor::spawn(chain_a, chain_b)?;
    supervisor.run()?;

    Ok(Output::success_msg("ok"))
}

fn start_all_connections(config: &Config) -> Result<Output, BoxError> {
    let connections = config
        .connections
        .as_ref()
        .filter(|conns| !conns.is_empty())
        .ok_or("no connections configured")?;

    let mut registry = Registry::new(config);

    let result = crossbeam_utils::thread::scope(|s| {
        for conn in connections {
            info!(
                "spawning supervisor for chains {} and {}",
                conn.a_chain, conn.b_chain
            );

            let chain_a = registry.get_or_spawn(&conn.a_chain)?;
            let chain_b = registry.get_or_spawn(&conn.b_chain)?;

            s.spawn(|_| {
                let supervisor = Supervisor::spawn(chain_a, chain_b).unwrap();
                supervisor.run()
            });
        }

        Ok(())
    });

    match result {
        Ok(Ok(())) => Ok(Output::success_msg("ok")),
        Ok(Err(e)) => Err(e),
        Err(e) => std::panic::resume_unwind(e),
    }
}

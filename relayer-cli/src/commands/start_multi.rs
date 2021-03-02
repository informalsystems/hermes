use abscissa_core::{Command, Options, Runnable};

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::{config::Config, supervisor::Supervisor};

use crate::commands::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,
}

impl Runnable for StartMultiCmd {
    fn run(&self) {
        let config = (*app_config()).clone();

        match start_multi(config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(output) => output.exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

fn start_multi(config: Config, chain_a: &ChainId, chain_b: &ChainId) -> Result<Output, BoxError> {
    let chains = ChainHandlePair::spawn(&config, chain_a, chain_b)?;
    let supervisor = Supervisor::spawn(chains.src, chains.dst)?;
    supervisor.run()?;

    Ok(Output::success("ok"))
}

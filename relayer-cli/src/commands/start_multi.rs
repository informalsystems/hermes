use abscissa_core::{config, Command, Options, Runnable};

use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::supervisor::Supervisor;

use crate::conclude::Output;
use crate::prelude::*;
use crate::{application::CliApp, commands::cli_utils::ChainHandlePair};

#[derive(Clone, Command, Debug, Options)]
pub struct StartMultiCmd {
    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,
}

impl Runnable for StartMultiCmd {
    fn run(&self) {
        let config = app_config();

        match start_multi(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(output) => output.exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

fn start_multi(
    config: &config::Reader<CliApp>,
    chain_a: &ChainId,
    chain_b: &ChainId,
) -> Result<Output, BoxError> {
    let chains = ChainHandlePair::spawn(config, chain_a, chain_b)?;
    let supervisor = Supervisor::spawn(chains.src, chains.dst)?;
    supervisor.run()?;

    Ok(Output::success("ok"))
}

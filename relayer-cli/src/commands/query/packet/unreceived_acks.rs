use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::chain::counterparty::unreceived_acknowledgements;
use ibc_relayer::chain::handle::BaseChainHandle;

use crate::cli_utils::spawn_chain_counterparty;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

/// This command does the following:
/// 1. queries the chain to get its counterparty, channel and port identifiers (needed in 2)
/// 2. queries the chain for all packet commitments/ sequences for a given port and channel
/// 3. queries the counterparty chain for the unacknowledged sequences out of the list obtained in 2.
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryUnreceivedAcknowledgementCmd {
    #[clap(
        required = true,
        help = "identifier of the chain to query the unreceived acknowledgments"
    )]
    chain_id: ChainId,

    #[clap(required = true, help = "port identifier")]
    port_id: PortId,

    #[clap(required = true, help = "channel identifier")]
    channel_id: ChannelId,
}

impl QueryUnreceivedAcknowledgementCmd {
    fn execute(&self) -> Result<Vec<u64>, Error> {
        let config = app_config();
        debug!("Options: {:?}", self);

        let (chains, channel) = spawn_chain_counterparty::<BaseChainHandle>(
            &config,
            &self.chain_id,
            &self.port_id,
            &self.channel_id,
        )?;

        debug!(
            "fetched from source chain {} the following channel {:?}",
            self.chain_id, channel
        );

        unreceived_acknowledgements(&chains.src, &chains.dst, &channel).map_err(Error::supervisor)
    }
}

impl Runnable for QueryUnreceivedAcknowledgementCmd {
    fn run(&self) {
        match self.execute() {
            Ok(seqs) => Output::success(seqs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

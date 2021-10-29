use abscissa_core::{Command, Options, Runnable};
use serde::Serialize;

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::ProdChainHandle;

use crate::cli_utils::spawn_chain_counterparty;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;
use ibc_relayer::chain::counterparty::acknowledgements_on_chain;

#[derive(Serialize, Debug)]
struct PacketSeqs {
    height: Height,
    seqs: Vec<u64>,
}

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketAcknowledgementsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,
}

impl QueryPacketAcknowledgementsCmd {
    fn execute(&self) -> Result<PacketSeqs, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let (chains, channel) = spawn_chain_counterparty::<ProdChainHandle>(
            &config,
            &self.chain_id,
            &self.port_id,
            &self.channel_id,
        )?;

        let (seqs, height) = acknowledgements_on_chain(&chains.src, &chains.dst, &channel)
            .map_err(Error::supervisor)?;

        Ok(PacketSeqs { seqs, height })
    }
}

// cargo run --bin hermes -- query packet acknowledgements ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketAcknowledgementsCmd {
    fn run(&self) {
        match self.execute() {
            Ok(ps) => Output::success(ps).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

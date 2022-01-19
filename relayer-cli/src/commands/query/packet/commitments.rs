use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use serde::Serialize;

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_relayer::chain::counterparty::commitments_on_chain;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

#[derive(Serialize, Debug)]
struct PacketSeqs {
    height: Height,
    seqs: Vec<u64>,
}

#[derive(Clone, Command, Debug, Parser)]
pub struct QueryPacketCommitmentsCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the port to query")]
    port_id: PortId,

    #[clap(required = true, help = "identifier of the channel to query")]
    channel_id: ChannelId,
}

impl QueryPacketCommitmentsCmd {
    fn execute(&self) -> Result<PacketSeqs, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        commitments_on_chain(&chain, &self.port_id, &self.channel_id)
            .map_err(Error::supervisor)
            .map(|(seqs_vec, height)| PacketSeqs {
                height,
                seqs: seqs_vec,
            })
    }
}

// cargo run --bin hermes -- query packet commitments ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketCommitmentsCmd {
    fn run(&self) {
        match self.execute() {
            Ok(p) => Output::success(p).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

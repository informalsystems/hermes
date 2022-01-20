use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use serde::Serialize;
use subtle_encoding::{Encoding, Hex};

use ibc::core::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;

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
pub struct QueryPacketCommitmentCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, help = "identifier of the port to query")]
    port_id: PortId,

    #[clap(required = true, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[clap(required = true, help = "sequence of packet to query")]
    sequence: Sequence,

    #[clap(short = 'H', long, help = "height of the state to query")]
    height: Option<u64>,
}

impl QueryPacketCommitmentCmd {
    fn execute(&self) -> Result<String, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        let bytes = chain
            .build_packet_proofs(
                PacketMsgType::Recv,
                &self.port_id,
                &self.channel_id,
                self.sequence,
                Height::new(chain.id().version(), self.height.unwrap_or(0_u64)),
            )
            .map(|(bytes, _)| bytes)
            .map_err(Error::relayer)?;

        if bytes.is_empty() {
            Ok("None".to_owned())
        } else {
            Ok(Hex::upper_case()
                .encode_to_string(bytes.clone())
                .unwrap_or_else(|_| format!("{:?}", bytes)))
        }
    }
}

impl Runnable for QueryPacketCommitmentCmd {
    fn run(&self) {
        match self.execute() {
            Ok(hex) => Output::success(hex).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

use abscissa_core::{Command, Options, Runnable};
use serde::Serialize;
use subtle_encoding::{Encoding, Hex};

use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Serialize, Debug)]
struct PacketSeqs {
    height: Height,
    seqs: Vec<u64>,
}

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketCommitmentCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(free, required, help = "sequence of packet to query")]
    sequence: Sequence,

    #[options(help = "height of the state to query", short = "h")]
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
            .map_err(|e| Kind::Query.context(e))?;

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

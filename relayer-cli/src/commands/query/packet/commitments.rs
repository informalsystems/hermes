use abscissa_core::{Command, Options, Runnable};
use serde::Serialize;

use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::{PacketState, QueryPacketCommitmentsRequest};

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
pub struct QueryPacketCommitmentsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,
}

impl QueryPacketCommitmentsCmd {
    fn execute(&self) -> Result<(Vec<PacketState>, Height), Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        let grpc_request = QueryPacketCommitmentsRequest {
            port_id: self.port_id.to_string(),
            channel_id: self.channel_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        chain
            .query_packet_commitments(grpc_request)
            .map_err(|e| Kind::Query.context(e).into())
    }
}

// cargo run --bin hermes -- query packet commitments ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketCommitmentsCmd {
    fn run(&self) {
        match self.execute() {
            Ok((packet_states, height)) => {
                // Transform the raw packet commitm. state into the list of sequence numbers
                let seqs: Vec<u64> = packet_states.iter().map(|ps| ps.sequence).collect();
                Output::success(PacketSeqs { height, seqs }).exit();
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

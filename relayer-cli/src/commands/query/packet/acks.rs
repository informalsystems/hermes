use abscissa_core::{Command, Options, Runnable};
use serde::Serialize;

use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::QueryPacketAcknowledgementsRequest;

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

        let chain = spawn_chain_runtime(&*config, &self.chain_id)?;

        let grpc_request = QueryPacketAcknowledgementsRequest {
            port_id: self.port_id.to_string(),
            channel_id: self.channel_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        // Transform the list fo raw packet state into the list of sequence numbers
        chain
            .query_packet_acknowledgements(grpc_request)
            .map_err(|e| Kind::Query.context(e).into())
            .map(|(packet, height)| PacketSeqs {
                seqs: packet.iter().map(|p| p.sequence).collect(),
                height,
            })
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

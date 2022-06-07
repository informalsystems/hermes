use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::requests::{IncludeProof, QueryPacketAcknowledgementRequest};
use subtle_encoding::{Encoding, Hex};

use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;
use crate::error::Error;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser)]
pub struct QueryPacketAcknowledgmentCmd {
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

impl QueryPacketAcknowledgmentCmd {
    fn execute(&self) -> Result<String, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        chain
            .query_packet_acknowledgement(
                QueryPacketAcknowledgementRequest {
                    port_id: self.port_id.clone(),
                    channel_id: self.channel_id,
                    sequence: self.sequence,
                    height: Height::new(chain.id().version(), self.height.unwrap_or(0_u64)),
                },
                IncludeProof::No,
            )
            .map_err(Error::relayer)
            .map(|(bytes, _)| {
                Hex::upper_case()
                    .encode_to_string(bytes.clone())
                    .unwrap_or_else(|_| format!("{:?}", bytes))
            })
    }
}

impl Runnable for QueryPacketAcknowledgmentCmd {
    fn run(&self) {
        match self.execute() {
            Ok(hex) => Output::success(hex).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

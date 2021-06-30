use abscissa_core::{Command, Options, Runnable};

use ibc::ics02_client::client_state::ClientState;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_proto::ibc::core::channel::v1::{
    QueryPacketAcknowledgementsRequest, QueryUnreceivedAcksRequest,
};
use ibc_relayer::chain::counterparty::channel_connection_client;

use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

/// This command does the following:
/// 1. queries the chain to get its counterparty, channel and port identifiers (needed in 2)
/// 2. queries the chain for all packet commitments/ sequences for a given port and channel
/// 3. queries the counterparty chain for the unacknowledged sequences out of the list obtained in 2.
#[derive(Clone, Command, Debug, Options)]
pub struct QueryUnreceivedAcknowledgementCmd {
    #[options(
        free,
        required,
        help = "identifier of the chain to query the unreceived acknowledgments"
    )]
    chain_id: ChainId,

    #[options(free, required, help = "port identifier")]
    port_id: PortId,

    #[options(free, required, help = "channel identifier")]
    channel_id: ChannelId,
}

impl QueryUnreceivedAcknowledgementCmd {
    fn execute(&self) -> Result<Vec<u64>, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        let channel_connection_client =
            channel_connection_client(chain.as_ref(), &self.port_id, &self.channel_id)
                .map_err(|e| Kind::Query.context(e))?;

        let channel = channel_connection_client.channel;
        debug!(
            "Fetched from chain {} the following channel {:?}",
            self.chain_id, channel
        );
        let counterparty_channel_id = channel
            .channel_end
            .counterparty()
            .channel_id
            .as_ref()
            .ok_or_else(|| {
                Kind::Query.context(format!(
                    "the channel {:?} has no counterparty channel id",
                    channel
                ))
            })?
            .to_string();

        let counterparty_chain_id = channel_connection_client.client.client_state.chain_id();
        let counterparty_chain = spawn_chain_runtime(&config, &counterparty_chain_id)?;

        // get the packet acknowledgments on counterparty chain
        let acks_request = QueryPacketAcknowledgementsRequest {
            port_id: channel.channel_end.counterparty().port_id.to_string(),
            channel_id: counterparty_channel_id,
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let sequences: Vec<u64> = counterparty_chain
            .query_packet_acknowledgements(acks_request)
            .map_err(|e| Kind::Query.context(e))
            // extract the sequences
            .map(|(packet_state, _)| packet_state.into_iter().map(|v| v.sequence).collect())?;

        let request = QueryUnreceivedAcksRequest {
            port_id: self.port_id.to_string(),
            channel_id: self.channel_id.to_string(),
            packet_ack_sequences: sequences,
        };

        chain
            .query_unreceived_acknowledgement(request)
            .map_err(|e| Kind::Query.context(e).into())
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

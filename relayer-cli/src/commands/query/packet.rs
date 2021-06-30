use abscissa_core::{Command, Options, Runnable};
use serde::Serialize;
use subtle_encoding::{Encoding, Hex};

use ibc::ics02_client::client_state::ClientState;
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_relayer::chain::counterparty::channel_connection_client;

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
    fn execute(&self) -> Result<Vec<u8>, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        chain
            .build_packet_proofs(
                PacketMsgType::Recv,
                &self.port_id,
                &self.channel_id,
                self.sequence,
                Height::new(chain.id().version(), self.height.unwrap_or(0_u64)),
            )
            .map(|(bytes, _)| bytes)
            .map_err(|e| Kind::Query.context(e).into())
    }
}

impl Runnable for QueryPacketCommitmentCmd {
    fn run(&self) {
        match self.execute() {
            Ok(bytes) if bytes.is_empty() => Output::success_msg("None").exit(),
            Ok(bytes) => {
                let hex = Hex::upper_case()
                    .encode_to_string(bytes)
                    .unwrap_or_else(|_| "[failed to encode bytes to hex]".to_owned());
                Output::success(hex).exit()
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// This command does the following:
/// 1. queries the chain to get its counterparty chain, channel and port identifiers (needed in 2)
/// 2. queries the counterparty chain for all packet commitments/ sequences for a given port and channel
/// 3. queries the chain for the unreceived sequences out of the list obtained in 2.
#[derive(Clone, Command, Debug, Options)]
pub struct QueryUnreceivedPacketsCmd {
    #[options(
        free,
        required,
        help = "identifier of the chain for the unreceived sequences"
    )]
    chain_id: ChainId,

    #[options(free, required, help = "port identifier")]
    port_id: PortId,

    #[options(free, required, help = "channel identifier")]
    channel_id: ChannelId,
}

impl QueryUnreceivedPacketsCmd {
    fn execute(&self) -> Result<Vec<u64>, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&*config, &self.chain_id)?;

        let channel_connection_client =
            channel_connection_client(chain.as_ref(), &self.port_id, &self.channel_id)
                .map_err(|e| Kind::Query.context(e))?;

        let channel = channel_connection_client.channel;
        debug!(
            "fetched from source chain {} the following channel {:?}",
            self.chain_id, channel
        );
        let counterparty_channel_id = channel
            .channel_end
            .counterparty()
            .channel_id
            .as_ref()
            .ok_or_else(|| {
                Kind::Query.context(format!(
                    "the channel {:?} counterparty has no channel id",
                    channel
                ))
            })?
            .to_string();

        let counterparty_chain_id = channel_connection_client.client.client_state.chain_id();
        let counterparty_chain = spawn_chain_runtime(&*config, &counterparty_chain_id)?;

        // get the packet commitments on the counterparty/ source chain
        let commitments_request = QueryPacketCommitmentsRequest {
            port_id: channel.channel_end.counterparty().port_id.to_string(),
            channel_id: counterparty_channel_id,
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let commitments = counterparty_chain
            .query_packet_commitments(commitments_request)
            .map_err(|e| Kind::Query.context(e))?;

        // extract the sequences
        let sequences: Vec<u64> = commitments.0.into_iter().map(|v| v.sequence).collect();

        debug!(
            "commitment sequence(s) obtained from counterparty chain {}: {:?}",
            counterparty_chain.id(),
            sequences
        );

        let request = QueryUnreceivedPacketsRequest {
            port_id: channel.port_id.to_string(),
            channel_id: channel.channel_id.to_string(),
            packet_commitment_sequences: sequences,
        };

        chain
            .query_unreceived_packets(request)
            .map_err(|e| Kind::Query.context(e).into())
    }
}

impl Runnable for QueryUnreceivedPacketsCmd {
    fn run(&self) {
        match self.execute() {
            Ok(seqs) => Output::success(seqs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
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
    fn execute(&self) -> Result<(Vec<u64>, Height), Error> {
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
            .map(|(packet, height)| (packet.iter().map(|p| p.sequence).collect(), height))
    }
}

// cargo run --bin hermes -- query packet acknowledgements ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketAcknowledgementsCmd {
    fn run(&self) {
        match self.execute() {
            Ok((seqs, height)) => {
                Output::success(PacketSeqs { height, seqs }).exit();
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketAcknowledgmentCmd {
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

impl QueryPacketAcknowledgmentCmd {
    fn execute(&self) -> Result<Vec<u8>, Error> {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain = spawn_chain_runtime(&config, &self.chain_id)?;

        chain
            .build_packet_proofs(
                PacketMsgType::Ack,
                &self.port_id,
                &self.channel_id,
                self.sequence,
                Height::new(chain.id().version(), self.height.unwrap_or(0_u64)),
            )
            .map(|(b, _)| b)
            .map_err(|e| Kind::Query.context(e).into())
    }
}

impl Runnable for QueryPacketAcknowledgmentCmd {
    fn run(&self) {
        match self.execute() {
            Ok(bytes) => {
                let hex = Hex::upper_case()
                    .encode_to_string(bytes)
                    .unwrap_or_else(|_| "[failed to encode bytes to hex]".to_owned());
                Output::success(hex).exit()
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

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

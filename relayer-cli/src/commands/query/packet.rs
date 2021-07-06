use alloc::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use serde::Serialize;
use subtle_encoding::{Encoding, Hex};
use tokio::runtime::Runtime as TokioRuntime;

use ibc::ics02_client::client_state::ClientState;
use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use ibc_relayer::chain::counterparty::channel_connection_client;
use ibc_relayer::chain::{runtime::ChainRuntime, CosmosSdkChain};

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

// cargo run --bin hermes -- query packet commitments ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketCommitmentsCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain_config = match config
            .find_chain(&self.chain_id)
            .ok_or_else(|| format!("chain '{}' not found in configuration file", self.chain_id))
        {
            Err(err) => return Output::error(err).exit(),
            Ok(result) => result,
        };

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let (chain, _) = ChainRuntime::<CosmosSdkChain>::spawn(chain_config.clone(), rt).unwrap();

        let grpc_request = QueryPacketCommitmentsRequest {
            port_id: self.port_id.to_string(),
            channel_id: self.channel_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let res: Result<(Vec<PacketState>, Height), Error> = chain
            .query_packet_commitments(grpc_request)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
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

impl Runnable for QueryPacketCommitmentCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain_config = match config.find_chain(&self.chain_id) {
            None => {
                return Output::error(format!(
                    "chain '{}' not found in configuration file",
                    self.chain_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };

        // cargo run --bin hermes -- query packet commitment ibc-0 transfer ibconexfer 3 --height 3
        let rt = Arc::new(TokioRuntime::new().unwrap());
        let (chain, _) = ChainRuntime::<CosmosSdkChain>::spawn(chain_config.clone(), rt).unwrap();

        let res = chain.build_packet_proofs(
            PacketMsgType::Recv,
            &self.port_id,
            &self.channel_id,
            self.sequence,
            Height::new(chain.id().version(), self.height.unwrap_or(0_u64)),
        );

        match res {
            Ok((bytes, _proofs)) if bytes.is_empty() => Output::success_msg("None").exit(),
            Ok((bytes, _proofs)) => {
                let hex = Hex::upper_case().encode_to_string(bytes).unwrap();
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

impl Runnable for QueryUnreceivedPacketsCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain_config = match config.find_chain(&self.chain_id) {
            None => {
                return Output::error(format!(
                    "chain '{}' not found in configuration file",
                    self.chain_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = match ChainRuntime::<CosmosSdkChain>::spawn(chain_config.clone(), rt.clone()) {
            Ok((chain, _)) => chain,
            Err(e) => {
                return Output::error(format!(
                    "error when spawning the chain runtime for {}: {}",
                    chain_config.id, e,
                ))
                .exit();
            }
        };

        let channel_connection_client =
            match channel_connection_client(chain.as_ref(), &self.port_id, &self.channel_id) {
                Ok(channel_connection_client) => channel_connection_client,
                Err(e) => {
                    return Output::error(format!(
                        "error when getting channel/ connection for {} on {}: {}",
                        self.channel_id,
                        chain.id(),
                        e,
                    ))
                    .exit();
                }
            };

        let channel = channel_connection_client.channel;
        debug!(
            "Fetched from source chain {} the following channel {:?}",
            self.chain_id, channel
        );

        let counterparty_chain_id = channel_connection_client.client.client_state.chain_id();
        let counterparty_chain_config = match config.find_chain(&counterparty_chain_id) {
            None => {
                return Output::error(format!(
                    "counterparty chain '{}' for channel '{}' not found in configuration file",
                    counterparty_chain_id, self.channel_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };

        let counterparty_chain =
            match ChainRuntime::<CosmosSdkChain>::spawn(counterparty_chain_config.clone(), rt) {
                Ok((chain, _)) => chain,
                Err(e) => {
                    return Output::error(format!(
                        "error when spawning the chain runtime for {}: {}",
                        chain_config.id, e,
                    ))
                    .exit();
                }
            };

        // get the packet commitments on the counterparty/ source chain
        let commitments_request = QueryPacketCommitmentsRequest {
            port_id: channel.channel_end.counterparty().port_id.to_string(),
            channel_id: channel
                .channel_end
                .counterparty()
                .channel_id
                .as_ref()
                .unwrap()
                .to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let seq_res = counterparty_chain
            .query_packet_commitments(commitments_request)
            .map_err(|e| Kind::Query.context(e));

        // extract the sequences
        let sequences: Vec<u64> = match seq_res {
            Ok(seqs) => seqs.0.into_iter().map(|v| v.sequence).collect(),
            Err(e) => {
                return Output::error(format!(
                    "failed to fetch the packet commitments from chain ({}) with error: {}",
                    chain.id(),
                    e
                ))
                .exit()
            }
        };

        let request = QueryUnreceivedPacketsRequest {
            port_id: channel.port_id.to_string(),
            channel_id: channel.channel_id.to_string(),
            packet_commitment_sequences: sequences,
        };

        let res = chain.query_unreceived_packets(request);

        match res {
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

// cargo run --bin hermes -- query packet acknowledgements ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketAcknowledgementsCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain_config = match config.find_chain(&self.chain_id) {
            None => {
                return Output::error(format!(
                    "chain '{}' not found in configuration file",
                    self.chain_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let (chain, _) = ChainRuntime::<CosmosSdkChain>::spawn(chain_config.clone(), rt).unwrap();
        let grpc_request = QueryPacketAcknowledgementsRequest {
            port_id: self.port_id.to_string(),
            channel_id: self.channel_id.to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let res: Result<(Vec<PacketState>, Height), Error> = chain
            .query_packet_acknowledgements(grpc_request)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
            Ok((packet_state, height)) => {
                // Transform the raw packet state into the list of sequence numbers
                let seqs: Vec<u64> = packet_state.iter().map(|ps| ps.sequence).collect();
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

impl Runnable for QueryPacketAcknowledgmentCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain_config = match config.find_chain(&self.chain_id) {
            None => {
                return Output::error(format!(
                    "chain '{}' not found in configuration file",
                    self.chain_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };

        // cargo run --bin hermes -- query packet acknowledgment ibc-0 transfer ibconexfer --height 3
        let rt = Arc::new(TokioRuntime::new().unwrap());
        let (chain, _) = ChainRuntime::<CosmosSdkChain>::spawn(chain_config.clone(), rt).unwrap();

        let res = chain.build_packet_proofs(
            PacketMsgType::Ack,
            &self.port_id,
            &self.channel_id,
            self.sequence,
            Height::new(chain.id().version(), self.height.unwrap_or(0_u64)),
        );

        match res {
            Ok((bytes, _proofs)) => {
                let hex = Hex::upper_case().encode_to_string(bytes).unwrap();
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

impl Runnable for QueryUnreceivedAcknowledgementCmd {
    fn run(&self) {
        let config = app_config();

        debug!("Options: {:?}", self);

        let chain_config = match config.find_chain(&self.chain_id) {
            None => {
                return Output::error(format!(
                    "chain '{}' not found in configuration file",
                    self.chain_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };
        let rt = Arc::new(TokioRuntime::new().unwrap());
        let (chain, _) =
            ChainRuntime::<CosmosSdkChain>::spawn(chain_config.clone(), rt.clone()).unwrap();

        let channel_connection_client =
            match channel_connection_client(chain.as_ref(), &self.port_id, &self.channel_id) {
                Ok(channel_connection_client) => channel_connection_client,
                Err(e) => {
                    return Output::error(format!(
                        "error when getting channel/ connection for {} on {}: {}",
                        self.channel_id,
                        chain.id(),
                        e,
                    ))
                    .exit();
                }
            };

        let channel = channel_connection_client.channel;
        debug!(
            "Fetched from chain {} the following channel {:?}",
            self.chain_id, channel
        );

        let counterparty_chain_id = channel_connection_client.client.client_state.chain_id();
        let counterparty_chain_config = match config.find_chain(&counterparty_chain_id) {
            None => {
                return Output::error(format!(
                    "counterparty chain '{}' for channel '{}' not found in configuration file",
                    counterparty_chain_id, self.channel_id
                ))
                .exit()
            }
            Some(chain_config) => chain_config,
        };

        let (counterparty_chain, _) =
            ChainRuntime::<CosmosSdkChain>::spawn(counterparty_chain_config.clone(), rt).unwrap();

        // get the packet acknowledgments on counterparty chain
        let acks_request = QueryPacketAcknowledgementsRequest {
            port_id: channel.channel_end.counterparty().port_id.to_string(),
            channel_id: channel
                .channel_end
                .counterparty()
                .channel_id
                .as_ref()
                .unwrap()
                .to_string(),
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };

        let seq_res = counterparty_chain
            .query_packet_acknowledgements(acks_request)
            .map_err(|e| Kind::Query.context(e));

        // extract the sequences
        let sequences: Vec<u64> = match seq_res {
            Ok(seqs) => seqs.0.into_iter().map(|v| v.sequence).collect(),
            Err(e) => {
                return Output::error(format!(
                    "failed to fetch packet acknowledgements from chain ({}) with error: {}",
                    chain.id(),
                    e
                ))
                .exit()
            }
        };

        let request = QueryUnreceivedAcksRequest {
            port_id: self.port_id.to_string(),
            channel_id: self.channel_id.to_string(),
            packet_ack_sequences: sequences,
        };

        let res = chain.query_unreceived_acknowledgement(request);

        match res {
            Ok(seqs) => Output::success(seqs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

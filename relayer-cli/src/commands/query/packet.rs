use std::sync::Arc;

use abscissa_core::{Command, Options, Runnable};
use serde_json::json;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::info;

use ibc::ics04_channel::packet::{PacketMsgType, Sequence};
use ibc::ics24_host::identifier::{ChannelId, PortId};
use ibc::Height;
use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryPacketAcknowledgementsRequest, QueryPacketCommitmentsRequest,
    QueryUnreceivedAcksRequest, QueryUnreceivedPacketsRequest,
};
use relayer::chain::{Chain, CosmosSDKChain, QueryPacketOptions};
use relayer::config::{ChainConfig, Config};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketCommitmentsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: String,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,
}

impl QueryPacketCommitmentsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryPacketOptions), String> {
        let dest_chain_config = config
            .find_chain(&self.chain_id.parse().unwrap())
            .ok_or_else(|| format!("missing configuration for chain ({}) ", self.chain_id))?;

        let opts = QueryPacketOptions {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
            height: self.height.unwrap_or(0_u64),
        };

        Ok((dest_chain_config.clone(), opts))
    }
}

// cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query packet commitments ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketCommitmentsCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let grpc_request = QueryPacketCommitmentsRequest {
            port_id: opts.port_id.to_string(),
            channel_id: opts.channel_id.to_string(),
            pagination: None,
        };

        let res: Result<(Vec<PacketState>, Height), Error> = chain
            .query_packet_commitments(grpc_request)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
            Ok(cs) => {
                // Transform the raw packet commitm. state into the list of sequence numbers
                let seqs: Vec<u64> = cs.0.iter().map(|ps| ps.sequence).collect();

                Output::success(seqs).with_result(json!(cs.1)).exit();
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketCommitmentCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: String,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(free, required, help = "sequence of packet to query")]
    sequence: u64,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,
}

impl QueryPacketCommitmentCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryPacketOptions, Sequence), String> {
        let dest_chain_config = config
            .find_chain(&self.chain_id.parse().unwrap())
            .ok_or_else(|| format!("missing configuration for chain ({}) ", self.chain_id))?;

        let opts = QueryPacketOptions {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
            height: self.height.unwrap_or(0_u64),
        };

        Ok((dest_chain_config.clone(), opts, self.sequence.into()))
    }
}

impl Runnable for QueryPacketCommitmentCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts, sequence) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        // run without proof:
        // cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query packet commitment ibc-0 transfer ibconexfer 3 --height 3
        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let res = chain.build_packet_proofs(
            PacketMsgType::Recv,
            &opts.port_id,
            &opts.channel_id,
            sequence,
            Height::new(0, opts.height),
        );

        match res {
            Ok(cs) => Output::success(cs.1).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// This command does the following:
/// 1. queries the source chain to get the counterparty channel and port identifiers (needed in 3)
/// 2. queries the source chain for all packet commitmments/ sequences for a given port and channel
/// 3. queries the destination chain for the unreceived sequences out of the list obtained in 2.
#[derive(Clone, Command, Debug, Options)]
pub struct QueryUnreceivedPacketsCmd {
    #[options(
        free,
        required,
        help = "identifier of the chain to query the unreceived sequences (dst chain)"
    )]
    dst_chain_id: String,

    #[options(
        free,
        required,
        help = "identifier of the chain where sent sequences are queried (source chain)"
    )]
    src_chain_id: String,

    #[options(
        free,
        required,
        help = "identifier of the port to query on source chain"
    )]
    port_id: PortId,

    #[options(
        free,
        required,
        help = "identifier of the channel to query on source chain"
    )]
    channel_id: ChannelId,
}

impl QueryUnreceivedPacketsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, ChainConfig, QueryPacketOptions), String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id.parse().unwrap())
            .ok_or_else(|| format!("missing configuration for chain ({}) ", self.src_chain_id))?;

        let dst_chain_config = config
            .find_chain(&self.dst_chain_id.parse().unwrap())
            .ok_or_else(|| format!("missing configuration for chain ({}) ", self.dst_chain_id))?;

        let opts = QueryPacketOptions {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
            height: 0_u64,
        };

        Ok((dst_chain_config.clone(), src_chain_config.clone(), opts))
    }
}

impl Runnable for QueryUnreceivedPacketsCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let src_chain = CosmosSDKChain::bootstrap(src_chain_config, rt.clone()).unwrap();
        let dst_chain = CosmosSDKChain::bootstrap(dst_chain_config, rt).unwrap();

        // get the channel information from source chain
        let channel_res = src_chain
            .query_channel(&opts.port_id, &opts.channel_id, Height::zero())
            .map_err(|e| Kind::Query.context(e));

        let channel = match channel_res {
            Ok(c) => c,
            Err(e) => {
                return Output::error(format!(
                    "failed to find channel ({}/{}) on chain ({}) with error: {}",
                    opts.port_id,
                    opts.channel_id,
                    src_chain.config().id,
                    e
                ))
                .exit();
            }
        };

        debug!(
            "Fetched from source chain {} the following channel {:?}",
            src_chain.config().id,
            channel
        );

        // get the packet commitments on source chain
        let commitments_request = QueryPacketCommitmentsRequest {
            port_id: opts.port_id.to_string(),
            channel_id: opts.channel_id.to_string(),
            pagination: None,
        };

        let seq_res = src_chain
            .query_packet_commitments(commitments_request)
            .map_err(|e| Kind::Query.context(e));

        // extract the sequences
        let sequences: Vec<u64> = match seq_res {
            Ok(seqs) => seqs.0.into_iter().map(|v| v.sequence).collect(),
            Err(e) => {
                return Output::error(format!(
                    "failed to fetch the packet commitments from src chain ({}) with error: {}",
                    src_chain.config().id,
                    e
                ))
                .exit()
            }
        };

        // Extract the channel identifier which the counterparty (dst chain) is using
        let channel_id: String = match &channel.counterparty().channel_id {
            None => {
                return Output::error(format!(
                    "The channel ({}/{}) has no counterparty (channel state is {:?})",
                    opts.port_id,
                    opts.channel_id,
                    *channel.state()
                ))
                .exit()
            }
            Some(id) => id.to_string(),
        };

        let request = QueryUnreceivedPacketsRequest {
            port_id: channel.counterparty().port_id().to_string(),
            channel_id,
            packet_commitment_sequences: sequences,
        };

        let res = dst_chain.query_unreceived_packets(request);

        match res {
            Ok(seqs) => Output::success(seqs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketAcknowledgementsCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: String,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,
}

impl QueryPacketAcknowledgementsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryPacketOptions), String> {
        let dest_chain_config = config
            .find_chain(&self.chain_id.parse().unwrap())
            .ok_or_else(|| {
                format!(
                    "missing configuration for the given chain ({}) ",
                    self.chain_id
                )
            })?;

        let opts = QueryPacketOptions {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
            height: self.height.unwrap_or(0_u64),
        };

        Ok((dest_chain_config.clone(), opts))
    }
}

// cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query packet acknowledgements ibc-0 transfer ibconexfer --height 3
impl Runnable for QueryPacketAcknowledgementsCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let grpc_request = QueryPacketAcknowledgementsRequest {
            port_id: opts.port_id.to_string(),
            channel_id: opts.channel_id.to_string(),
            pagination: None,
        };

        let res: Result<(Vec<PacketState>, Height), Error> = chain
            .query_packet_acknowledgements(grpc_request)
            .map_err(|e| Kind::Query.context(e).into());

        match res {
            Ok(ps) => {
                // Transform the raw packet state into the list of acks. sequence numbers
                let seqs: Vec<u64> = ps.0.iter().map(|ps| ps.sequence).collect();

                Output::success(seqs).with_result(json!(ps.1)).exit();
            }
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketAcknowledgmentCmd {
    #[options(free, required, help = "identifier of the chain to query")]
    chain_id: String,

    #[options(free, required, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, required, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(free, required, help = "sequence of packet to query")]
    sequence: u64,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,
}

impl QueryPacketAcknowledgmentCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryPacketOptions, Sequence), String> {
        let dest_chain_config = config
            .find_chain(&self.chain_id.parse().unwrap())
            .ok_or_else(|| format!("missing configuration for chain ({}) ", self.chain_id))?;

        let opts = QueryPacketOptions {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
            height: self.height.unwrap_or(0_u64),
        };

        Ok((dest_chain_config.clone(), opts, self.sequence.into()))
    }
}

impl Runnable for QueryPacketAcknowledgmentCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts, sequence) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        // run without proof:
        // cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query packet acknowledgment ibc-0 transfer ibconexfer --height 3
        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let res = chain.build_packet_proofs(
            PacketMsgType::Ack,
            &opts.port_id,
            &opts.channel_id,
            sequence,
            Height::new(0, opts.height),
        );

        match res {
            Ok(out) => Output::success(out).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

/// This command does the following:
/// 1. queries the source chain to get the counterparty channel and port identifiers (needed in 3)
/// 2. queries the source chain for all packet commitmments/ sequences for a given port and channel
/// 3. queries the destination chain for the unreceived sequences out of the list obtained in 2.
#[derive(Clone, Command, Debug, Options)]
pub struct QueryUnreceivedAcknowledgementCmd {
    #[options(
        free,
        required,
        help = "identifier of the chain to query the unreceived acks (dst chain)"
    )]
    dst_chain_id: String,

    #[options(
        free,
        required,
        help = "identifier of the chain where received sequences are queried (source chain)"
    )]
    src_chain_id: String,

    #[options(
        free,
        required,
        help = "identifier of the port to query on source chain"
    )]
    port_id: PortId,

    #[options(
        free,
        required,
        help = "identifier of the channel to query on source chain"
    )]
    channel_id: ChannelId,
}

impl QueryUnreceivedAcknowledgementCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, ChainConfig, QueryPacketOptions), String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id.parse().unwrap())
            .ok_or_else(|| format!("missing configuration for chain ({}) ", self.src_chain_id))?;

        let dst_chain_config = config
            .find_chain(&self.dst_chain_id.parse().unwrap())
            .ok_or_else(|| format!("missing configuration for chain ({}) ", self.dst_chain_id))?;

        let opts = QueryPacketOptions {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
            height: 0_u64,
        };

        Ok((dst_chain_config.clone(), src_chain_config.clone(), opts))
    }
}

impl Runnable for QueryUnreceivedAcknowledgementCmd {
    fn run(&self) {
        let config = app_config();

        let (dst_chain_config, src_chain_config, opts) = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Options {:?}", opts);

        let rt = Arc::new(TokioRuntime::new().unwrap());
        let src_chain = CosmosSDKChain::bootstrap(src_chain_config, rt.clone()).unwrap();
        let dst_chain = CosmosSDKChain::bootstrap(dst_chain_config, rt).unwrap();

        // get the channel information from source chain
        let channel_res = src_chain
            .query_channel(&opts.port_id, &opts.channel_id, Height::zero())
            .map_err(|e| Kind::Query.context(e));

        let channel = match channel_res {
            Ok(c) => c,
            Err(e) => {
                return Output::error(format!(
                    "failed to find the target channel ({}/{}) on src chain ({}) with error: {}",
                    opts.port_id,
                    opts.channel_id,
                    src_chain.config().id,
                    e
                ))
                .exit();
            }
        };

        debug!(
            "Fetched from src chain {} the following channel {:?}",
            src_chain.config().id,
            channel
        );

        // get the packet commitments on source chain
        let acks_request = QueryPacketAcknowledgementsRequest {
            port_id: opts.port_id.to_string(),
            channel_id: opts.channel_id.to_string(),
            pagination: None,
        };

        let seq_res = src_chain
            .query_packet_acknowledgements(acks_request)
            .map_err(|e| Kind::Query.context(e));

        // extract the sequences
        let sequences: Vec<u64> = match seq_res {
            Ok(seqs) => seqs.0.into_iter().map(|v| v.sequence).collect(),
            Err(e) => {
                return Output::error(format!(
                    "failed to fetch packet acknowledgements from src chain ({}) with error: {}",
                    src_chain.config().id,
                    e
                ))
                .exit()
            }
        };

        let channel_id = match &channel.counterparty().channel_id() {
            None => {
                return Output::error(format!(
                    "The channel ({}/{}) has no counterparty (channel state is {:?})",
                    opts.port_id,
                    opts.channel_id,
                    *channel.state()
                ))
                .exit()
            }
            Some(id) => id.to_string(),
        };

        let request = QueryUnreceivedAcksRequest {
            port_id: channel.counterparty().port_id().to_string(),
            channel_id,
            packet_ack_sequences: sequences,
        };

        let res = dst_chain.query_unreceived_acknowledgements(request);

        match res {
            Ok(seqs) => Output::success(seqs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

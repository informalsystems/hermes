use std::sync::{Arc, Mutex};
use tokio::runtime::Runtime as TokioRuntime;

use abscissa_core::{Command, Options, Runnable};

use ibc_proto::ibc::core::channel::v1::{
    PacketState, QueryPacketCommitmentsRequest, QueryUnreceivedPacketsRequest,
};

use ibc::ics24_host::identifier::{ChannelId, PortId};
use ibc::Height;

use relayer::chain::{Chain, CosmosSDKChain, QueryPacketOptions};
use relayer::config::{ChainConfig, Config};

use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketCommitmentsCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: String,

    #[options(free, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, help = "identifier of the channel to query")]
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
            .chains
            .iter()
            .find(|c| c.id == self.chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

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
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Options", "{:?}", opts);

        let rt = Arc::new(Mutex::new(TokioRuntime::new().unwrap()));
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
            Ok(cs) => status_info!(
                "Result for packet commitments query at height",
                "{:?} {:#?}",
                cs.0,
                cs.1
            ),
            Err(e) => status_info!("Error encountered on packet commitments query:", "{}", e),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct QueryPacketCommitmentCmd {
    #[options(free, help = "identifier of the chain to query")]
    chain_id: String,

    #[options(free, help = "identifier of the port to query")]
    port_id: PortId,

    #[options(free, help = "identifier of the channel to query")]
    channel_id: ChannelId,

    #[options(free, help = "sequence of packet to query")]
    sequence: u64,

    #[options(help = "height of the state to query", short = "h")]
    height: Option<u64>,
}

impl QueryPacketCommitmentCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, QueryPacketOptions, u64), String> {
        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let opts = QueryPacketOptions {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id.clone(),
            height: self.height.unwrap_or(0_u64),
        };

        Ok((dest_chain_config.clone(), opts, self.sequence))
    }
}

impl Runnable for QueryPacketCommitmentCmd {
    fn run(&self) {
        let config = app_config();

        let (chain_config, opts, sequence) = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Options", "{:?}", opts);

        // run without proof:
        // cargo run --bin relayer -- -c relayer/tests/config/fixtures/simple_config.toml query packet commitments ibc-0 transfer ibconexfer --height 3
        let rt = Arc::new(Mutex::new(TokioRuntime::new().unwrap()));
        let chain = CosmosSDKChain::bootstrap(chain_config, rt).unwrap();

        let res = chain.proven_packet_commitment(
            &opts.port_id,
            &opts.channel_id,
            sequence,
            Height::new(0, opts.height),
        );

        match res {
            Ok(cs) => status_info!(
                "Result for packet commitments query at height",
                "{:?} {:#?}",
                cs.0,
                cs.1
            ),
            Err(e) => status_info!("Error encountered on packet commitments query:", "{}", e),
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
        help = "identifier of the chain to query the unreceived sequences"
    )]
    dst_chain_id: String,

    #[options(
        free,
        help = "identifier of the chain where sent sequences are queried"
    )]
    src_chain_id: String,

    #[options(free, help = "identifier of the port to query on source chain")]
    port_id: PortId,

    #[options(free, help = "identifier of the channel to query on source chain")]
    channel_id: ChannelId,
}

impl QueryUnreceivedPacketsCmd {
    fn validate_options(
        &self,
        config: &Config,
    ) -> Result<(ChainConfig, ChainConfig, QueryPacketOptions), String> {
        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let dst_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.dst_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

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
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Options", "{:?}", opts);

        let rt = Arc::new(Mutex::new(TokioRuntime::new().unwrap()));
        let src_chain = CosmosSDKChain::bootstrap(src_chain_config, rt.clone()).unwrap();
        let dst_chain = CosmosSDKChain::bootstrap(dst_chain_config, rt).unwrap();

        // get the channel information from source chain
        let channel = src_chain
            .query_channel(&opts.port_id, &opts.channel_id, Height::zero())
            .unwrap();

        // get the packet commitments on source chain
        let commitments_request = QueryPacketCommitmentsRequest {
            port_id: opts.port_id.to_string(),
            channel_id: opts.channel_id.to_string(),
            pagination: None,
        };

        // extract the sequences
        let sequences: Vec<u64> = src_chain
            .query_packet_commitments(commitments_request)
            .unwrap()
            .0
            .into_iter()
            .map(|v| v.sequence)
            .collect();

        let request = QueryUnreceivedPacketsRequest {
            port_id: channel.counterparty().port_id().to_string(),
            channel_id: channel.counterparty().channel_id().unwrap().to_string(),
            packet_commitment_sequences: sequences,
        };

        let res = dst_chain.query_unreceived_packets(request);

        match res {
            Ok(cs) => status_info!("Result for unreceived packets query", "{:?}", cs),
            Err(e) => status_info!("Error encountered on packet commitments query:", "{}", e),
        }
    }
}

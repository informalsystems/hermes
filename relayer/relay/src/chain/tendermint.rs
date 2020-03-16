use std::time::Duration;

use tendermint::block::signed_header::SignedHeader as TMCommit;
use tendermint::block::Header as TMHeader;
use tendermint::lite::TrustThresholdFraction;
use tendermint::rpc::Client as RpcClient;

use relayer_modules::ics02_client::client_type::Tendermint;
use relayer_modules::ics07_tendermint::consensus_state::ConsensusState;

use crate::client::rpc_requester::RpcRequester;
use crate::config::ChainConfig;
use crate::error;

use super::Chain;

pub struct TendermintChain {
    config: ChainConfig,
    rpc_client: RpcClient,
    requester: RpcRequester,
}

impl TendermintChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, error::Error> {
        // TODO: Derive Clone on RpcClient in tendermint-rs
        let requester = RpcRequester::new(RpcClient::new(config.rpc_addr.clone()));
        let rpc_client = RpcClient::new(config.rpc_addr.clone());

        Ok(Self {
            config,
            rpc_client,
            requester,
        })
    }
}

impl Chain for TendermintChain {
    type Type = Tendermint;
    type Header = TMHeader;
    type Commit = TMCommit;
    type ConsensusState = ConsensusState;
    type Requester = RpcRequester;

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn rpc_client(&self) -> &RpcClient {
        &self.rpc_client
    }

    fn requester(&self) -> &Self::Requester {
        &self.requester
    }

    fn trusting_period(&self) -> Duration {
        self.config.trusting_period
    }

    fn trust_threshold(&self) -> TrustThresholdFraction {
        TrustThresholdFraction::default()
    }
}

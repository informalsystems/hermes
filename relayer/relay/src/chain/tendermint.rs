use tendermint::block::signed_header::SignedHeader as TMCommit;
use tendermint::block::Header as TMHeader;
use tendermint::rpc::Client as RpcClient;

use tendermint_lite::requester::RPCRequester;

use relayer_modules::ics02_client::client_type::Tendermint;
use relayer_modules::ics07_tendermint::consensus_state::ConsensusState;

use crate::config::ChainConfig;
use crate::error;

use super::Chain;

pub struct TendermintChain {
    config: ChainConfig,
    rpc_client: RpcClient,
    requester: RPCRequester,
}

impl TendermintChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, error::Error> {
        // TODO: Derive Clone on RpcClient in tendermint-rs
        let requester = RPCRequester::new(RpcClient::new(config.rpc_addr.clone()));
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
    type Requester = RPCRequester;

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn rpc_client(&self) -> &RpcClient {
        &self.rpc_client
    }

    fn requester(&self) -> &Self::Requester {
        &self.requester
    }
}

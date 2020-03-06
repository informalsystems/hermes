use tendermint::rpc;

use relayer_modules::ics02_client::client_type::Tendermint;
use relayer_modules::ics07_tendermint::consensus_state::ConsensusState;

use crate::config::ChainConfig;
use crate::error;

use super::Chain;

pub struct TendermintChain {
    config: ChainConfig,
    rpc_client: rpc::Client,
}

impl TendermintChain {
    pub fn from_config(config: ChainConfig) -> Result<Self, error::Error> {
        let rpc_client = rpc::Client::new(config.rpc_addr.clone());
        Ok(Self { config, rpc_client })
    }
}

impl Chain for TendermintChain {
    type Type = Tendermint;
    type ConsensusState = ConsensusState;

    fn config(&self) -> &ChainConfig {
        &self.config
    }

    fn rpc_client(&self) -> &rpc::Client {
        &self.rpc_client
    }
}

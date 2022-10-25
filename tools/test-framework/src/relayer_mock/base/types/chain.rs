use std::collections::HashMap;
use std::sync::Arc;
use std::time::SystemTime;

use ibc_relayer_framework::base::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::relayer_mock::base::types::runtime::MockRuntimeContext;

pub struct MockChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub runtime: OfaRuntimeContext<MockRuntimeContext>,
    clients_consensus: HashMap<String, ConsensusState>,
}

impl<Chain> MockChainWrapper<Chain> {
    pub fn new(
        chain: Arc<Chain>,
        runtime: OfaRuntimeContext<MockRuntimeContext>,
        clients_consensus: HashMap<String, ConsensusState>,
    ) -> Self {
        MockChainWrapper {
            chain,
            runtime,
            clients_consensus,
        }
    }

    pub fn query_consensus_state(&self, client_id: &String) -> Option<&ConsensusState> {
        self.clients_consensus.get(client_id)
    }
}

#[derive(Clone)]
pub struct ConsensusState {}

pub struct ChainStatus {
    pub height: u128,
    pub timestamp: SystemTime,
}

impl Default for ChainStatus {
    fn default() -> Self {
        ChainStatus {
            height: 1,
            timestamp: SystemTime::now(),
        }
    }
}

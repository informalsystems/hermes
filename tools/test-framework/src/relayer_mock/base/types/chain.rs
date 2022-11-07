use crate::relayer_mock::base::types::height::Height;

use super::state::State;

#[derive(Clone)]
pub struct ConsensusState {}

impl From<State> for ConsensusState {
    fn from(_: State) -> Self {
        ConsensusState {}
    }
}

#[derive(Debug)]
pub struct ChainStatus {
    pub height: u128,
    pub timestamp: Height,
}

impl ChainStatus {
    pub fn new(height: u128, timestamp: Height) -> Self {
        Self { height, timestamp }
    }
}

impl Default for ChainStatus {
    fn default() -> Self {
        ChainStatus {
            height: 1,
            timestamp: Height(1),
        }
    }
}

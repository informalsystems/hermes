use std::time::SystemTime;

use super::state::State;

#[derive(Clone)]
pub struct ConsensusState {}

impl From<State> for ConsensusState {
    fn from(_: State) -> Self {
        ConsensusState {}
    }
}

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

use crate::tests::relayer_mock::base::types::height::Height;
use crate::tests::relayer_mock::base::types::state::State;

#[derive(Clone)]
pub struct ConsensusState {}

impl From<State> for ConsensusState {
    fn from(_: State) -> Self {
        ConsensusState {}
    }
}

#[derive(Debug)]
pub struct ChainStatus {
    pub height: Height,
    pub timestamp: Height,
}

impl ChainStatus {
    pub fn new(height: Height, timestamp: Height) -> Self {
        Self { height, timestamp }
    }
}

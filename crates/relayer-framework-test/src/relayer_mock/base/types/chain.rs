use crate::relayer_mock::base::types::height::Height;
use crate::relayer_mock::base::types::state::State;

#[derive(Clone, Debug)]
pub struct MockChainStatus {
    pub height: Height,
    pub timestamp: Height,
    pub state: State,
}

impl MockChainStatus {
    pub fn new(height: Height, timestamp: Height, state: State) -> Self {
        Self {
            height,
            timestamp,
            state,
        }
    }
}

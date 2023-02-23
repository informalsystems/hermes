use crate::relayer_mock::base::types::aliases::MockTimestamp;
use crate::relayer_mock::base::types::height::Height;
use crate::relayer_mock::base::types::state::State;

#[derive(Clone, Debug)]
pub struct MockChainStatus {
    pub height: Height,
    pub timestamp: MockTimestamp,
    pub state: State,
}

impl MockChainStatus {
    pub fn new(height: Height, timestamp: MockTimestamp, state: State) -> Self {
        Self {
            height,
            timestamp,
            state,
        }
    }
}

impl From<(Height, MockTimestamp, State)> for MockChainStatus {
    fn from(s: (Height, MockTimestamp, State)) -> Self {
        MockChainStatus {
            height: s.0,
            timestamp: s.1,
            state: s.2,
        }
    }
}

use serde_derive::{Deserialize, Serialize};
use tendermint::block::Height;

#[cfg(test)]
use crate::ics02_client::client_def::AnyConsensusState;
#[cfg(test)]
use crate::mock_client::header::MockHeader;
#[cfg(test)]
use crate::mock_client::state::MockConsensusState;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SelfHeader {
    // Tendermint(tendermint::header::Header),
    #[cfg(test)]
    Mock(MockHeader),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistoricalInfo {
    pub header: SelfHeader,
}

#[cfg(test)]
impl From<MockHeader> for AnyConsensusState {
    fn from(h: MockHeader) -> Self {
        AnyConsensusState::Mock(MockConsensusState(h))
    }
}

pub trait ChainReader {
    fn self_historical_info(&self, height: Height) -> Option<&HistoricalInfo>;
}

pub trait ChainKeeper {
    fn store_historical_info(&mut self, height: Height, info: HistoricalInfo);
}

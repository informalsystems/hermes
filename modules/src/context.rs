use crate::ics02_client::client_def::AnyConsensusState;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::MockConsensusState;
use serde_derive::{Deserialize, Serialize};
use tendermint::block::Height;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SelfHeader {
    Mock(MockHeader),
    //Tendermint(tendermint::header::Header),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HistoricalInfo {
    pub header: SelfHeader,
}

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

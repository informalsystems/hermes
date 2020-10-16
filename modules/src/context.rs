use serde_derive::{Deserialize, Serialize};

use crate::ics02_client::client_def::AnyConsensusState;
use crate::ics02_client::client_def::AnyHeader;
use crate::Height;

#[cfg(test)]
use {crate::mock_client::header::MockHeader, crate::mock_client::state::MockConsensusState};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SelfChainType {
    Tendermint,
    #[cfg(test)]
    Mock,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum SelfHeader {
    Tendermint(crate::ics07_tendermint::header::Header),
    #[cfg(test)]
    Mock(MockHeader),
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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
    fn self_historical_info(&self, height: Height) -> Option<HistoricalInfo>;
    fn header(&self, height: Height) -> Option<AnyHeader>;
    fn fetch_self_consensus_state(&self, height: Height) -> Option<AnyConsensusState>;
}

pub trait ChainKeeper {
    fn store_historical_info(&mut self, height: Height, info: HistoricalInfo);
}

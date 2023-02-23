use std::collections::HashMap;
use std::convert::From;
use std::fmt::{self, Display};

use super::height::Height;
use crate::relayer_mock::base::types::chain::MockChainStatus;
use crate::relayer_mock::base::types::state::State;

pub type PacketUID = (PortId, ChannelId, Sequence);
pub type ConsensusState = State;
pub type ChainState = State;
pub type ClientId = String;
pub type ChannelId = String;
pub type PortId = String;
pub type ChainStatus = MockChainStatus;
pub type Sequence = u128;
pub type StateStore = HashMap<Height, ChainState>;

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub struct MockTimestamp(pub u128);

impl Display for MockTimestamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for MockTimestamp {
    fn default() -> Self {
        MockTimestamp(1000)
    }
}

impl From<u128> for MockTimestamp {
    fn from(u: u128) -> Self {
        MockTimestamp(u)
    }
}

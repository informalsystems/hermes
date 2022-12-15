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
pub type MockTimestamp = u128;

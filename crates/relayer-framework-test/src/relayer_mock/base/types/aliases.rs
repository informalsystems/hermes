use std::collections::HashMap;

use ibc_relayer_framework::base::one_for_all::traits::chain::OfaChainTypes;

use crate::relayer_mock;
use crate::relayer_mock::base::types::height::Height as MockHeight;

pub type PacketUID = (PortId, ChannelId, Sequence);
pub type ConsensusState =
    <relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::ConsensusState;
pub type ChainState = HashMap<MockHeight, ConsensusState>;
pub type ClientId = <relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::ClientId;
pub type ChannelId = <relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::ChannelId;
pub type PortId = <relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::PortId;
pub type ChainStatus =
    <relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::ChainStatus;
pub type Sequence = <relayer_mock::contexts::chain::MockChainContext as OfaChainTypes>::Sequence;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::chain::traits::types::chain_id::HasChainIdType;
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::base::relay::traits::types::HasRelayTypes;

pub type RelayAToB<Builder> = <<Builder as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayAToB;

pub type RelayBToA<Builder> = <<Builder as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayBToA;

pub type ChainA<Builder> = <RelayAToB<Builder> as HasRelayTypes>::SrcChain;

pub type ChainB<Builder> = <RelayAToB<Builder> as HasRelayTypes>::DstChain;

pub type ChainIdA<Builder> = <ChainA<Builder> as HasChainIdType>::ChainId;

pub type ChainIdB<Builder> = <ChainA<Builder> as HasChainIdType>::ChainId;

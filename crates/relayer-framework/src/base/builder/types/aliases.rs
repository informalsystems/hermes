use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::chain::traits::types::chain_id::HasChainIdType;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::runtime::HasRuntime;

pub type RelayAToB<Builder> = <<Builder as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayAToB;

pub type RelayBToA<Builder> = <<Builder as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayBToA;

pub type ChainA<Builder> = <RelayAToB<Builder> as HasRelayTypes>::SrcChain;

pub type ChainB<Builder> = <RelayAToB<Builder> as HasRelayTypes>::DstChain;

pub type ChainIdA<Builder> = <ChainA<Builder> as HasChainIdType>::ChainId;

pub type ChainIdB<Builder> = <ChainA<Builder> as HasChainIdType>::ChainId;

pub type ClientIdA<Builder> = <ChainA<Builder> as HasIbcChainTypes<ChainB<Builder>>>::ClientId;

pub type ClientIdB<Builder> = <ChainB<Builder> as HasIbcChainTypes<ChainA<Builder>>>::ClientId;

pub type Runtime<Builder> = <Builder as HasRuntime>::Runtime;

pub type Mutex<Builder, T> = <Runtime<Builder> as HasMutex>::Mutex<T>;

pub type ChainACache<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdA<Builder>, ChainA<Builder>>>>;

pub type ChainBCache<Builder> = Arc<Mutex<Builder, BTreeMap<ChainIdB<Builder>, ChainB<Builder>>>>;

pub type RelayAToBCache<Builder> =
    Arc<Mutex<Builder, BTreeMap<(ChainIdA<Builder>, ChainIdB<Builder>), RelayAToB<Builder>>>>;

pub type RelayBToACache<Builder> =
    Arc<Mutex<Builder, BTreeMap<(ChainIdB<Builder>, ChainIdA<Builder>), RelayBToA<Builder>>>>;

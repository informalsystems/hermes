use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use crate::base::builder::traits::birelay::HasBiRelayType;
use crate::base::chain::traits::types::chain_id::HasChainIdType;
use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::two_way::HasTwoWayRelay;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::types::aliases::Mutex;

pub type RelayAToB<Build> = <<Build as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayAToB;

pub type RelayBToA<Build> = <<Build as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayBToA;

pub type ChainA<Build> = <RelayAToB<Build> as HasRelayTypes>::SrcChain;

pub type ChainB<Build> = <RelayAToB<Build> as HasRelayTypes>::DstChain;

pub type ChainIdA<Build> = <ChainA<Build> as HasChainIdType>::ChainId;

pub type ChainIdB<Build> = <ChainB<Build> as HasChainIdType>::ChainId;

pub type ClientIdA<Build> = <ChainA<Build> as HasIbcChainTypes<ChainB<Build>>>::ClientId;

pub type ClientIdB<Build> = <ChainB<Build> as HasIbcChainTypes<ChainA<Build>>>::ClientId;

pub type ChainACache<Build> = Arc<Mutex<Build, BTreeMap<ChainIdA<Build>, ChainA<Build>>>>;

pub type ChainBCache<Build> = Arc<Mutex<Build, BTreeMap<ChainIdB<Build>, ChainB<Build>>>>;

pub type RelayError<Build> = <RelayAToB<Build> as HasErrorType>::Error;

pub type RelayAToBCache<Build> = Arc<
    Mutex<
        Build,
        BTreeMap<
            (
                ChainIdA<Build>,
                ChainIdB<Build>,
                ClientIdA<Build>,
                ClientIdB<Build>,
            ),
            RelayAToB<Build>,
        >,
    >,
>;

pub type RelayBToACache<Build> = Arc<
    Mutex<
        Build,
        BTreeMap<
            (
                ChainIdB<Build>,
                ChainIdA<Build>,
                ClientIdB<Build>,
                ClientIdA<Build>,
            ),
            RelayBToA<Build>,
        >,
    >,
>;

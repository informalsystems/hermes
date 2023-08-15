use alloc::collections::BTreeMap;

use crate::builder::traits::birelay::types::HasBiRelayType;
use crate::builder::traits::target::chain::ChainBuildTarget;
use crate::builder::traits::target::relay::RelayBuildTarget;
use crate::chain::traits::types::chain_id::HasChainIdType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::error::HasErrorType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::two_way::HasTwoWayRelay;
use crate::runtime::traits::runtime::HasRuntime;
use crate::runtime::types::aliases::Mutex;

pub type RelayAToB<Build> = <<Build as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayAToB;

pub type RelayBToA<Build> = <<Build as HasBiRelayType>::BiRelay as HasTwoWayRelay>::RelayBToA;

pub type ChainA<Build> = <RelayAToB<Build> as HasRelayChains>::SrcChain;

pub type ChainB<Build> = <RelayAToB<Build> as HasRelayChains>::DstChain;

pub type ChainIdA<Build> = <ChainA<Build> as HasChainIdType>::ChainId;

pub type ChainIdB<Build> = <ChainB<Build> as HasChainIdType>::ChainId;

pub type ClientIdA<Build> = <ChainA<Build> as HasIbcChainTypes<ChainB<Build>>>::ClientId;

pub type ClientIdB<Build> = <ChainB<Build> as HasIbcChainTypes<ChainA<Build>>>::ClientId;

pub type ChainACache<Build> = Mutex<Build, BTreeMap<ChainIdA<Build>, ChainA<Build>>>;

pub type ChainBCache<Build> = Mutex<Build, BTreeMap<ChainIdB<Build>, ChainB<Build>>>;

pub type RelayError<Build> = <RelayAToB<Build> as HasErrorType>::Error;

pub type RelayAToBCache<Build> = Mutex<
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
>;

pub type RelayBToACache<Build> = Mutex<
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
>;

pub type TargetChain<Build, Target> = <Target as ChainBuildTarget<Build>>::TargetChain;

pub type TargetChainRuntime<Build, Target> = <TargetChain<Build, Target> as HasRuntime>::Runtime;

pub type TargetChainId<Build, Target> = <TargetChain<Build, Target> as HasChainIdType>::ChainId;

pub type TargetClientId<Build, Target> =
    <TargetChain<Build, Target> as HasIbcChainTypes<CounterpartyChain<Build, Target>>>::ClientId;

pub type CounterpartyChain<Build, Target> = <Target as ChainBuildTarget<Build>>::CounterpartyChain;

pub type CounterpartyChainId<Build, Target> =
    <CounterpartyChain<Build, Target> as HasChainIdType>::ChainId;

pub type CounterpartyClientId<Build, Target> =
    <CounterpartyChain<Build, Target> as HasIbcChainTypes<TargetChain<Build, Target>>>::ClientId;

pub type TargetChainCache<Build, Target> =
    Mutex<Build, BTreeMap<TargetChainId<Build, Target>, TargetChain<Build, Target>>>;

pub type TargetRelay<Build, Target> = <Target as RelayBuildTarget<Build>>::TargetRelay;

pub type TargetRelayError<Build, Target> = <TargetRelay<Build, Target> as HasErrorType>::Error;

pub type SrcChainTarget<Build, Target> = <Target as RelayBuildTarget<Build>>::SrcChainTarget;

pub type DstChainTarget<Build, Target> = <Target as RelayBuildTarget<Build>>::DstChainTarget;

pub type TargetSrcChain<Build, Target> = <TargetRelay<Build, Target> as HasRelayChains>::SrcChain;

pub type TargetDstChain<Build, Target> = <TargetRelay<Build, Target> as HasRelayChains>::DstChain;

pub type TargetSrcChainId<Build, Target> =
    <TargetSrcChain<Build, Target> as HasChainIdType>::ChainId;

pub type TargetDstChainId<Build, Target> =
    <TargetDstChain<Build, Target> as HasChainIdType>::ChainId;

pub type TargetSrcClientId<Build, Target> =
    <TargetSrcChain<Build, Target> as HasIbcChainTypes<TargetDstChain<Build, Target>>>::ClientId;

pub type TargetDstClientId<Build, Target> =
    <TargetDstChain<Build, Target> as HasIbcChainTypes<TargetSrcChain<Build, Target>>>::ClientId;

pub type TargetRelayCache<Build, Target> = Mutex<
    Build,
    BTreeMap<
        (
            TargetSrcChainId<Build, Target>,
            TargetDstChainId<Build, Target>,
            TargetSrcClientId<Build, Target>,
            TargetDstClientId<Build, Target>,
        ),
        TargetRelay<Build, Target>,
    >,
>;

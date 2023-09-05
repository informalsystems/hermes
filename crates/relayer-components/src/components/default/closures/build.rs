use crate::build::traits::birelay::HasBiRelayType;
use crate::build::traits::cache::{HasChainCache, HasRelayCache};
use crate::build::traits::components::birelay_builder::CanBuildBiRelay;
use crate::build::traits::components::birelay_from_relay_builder::BiRelayFromRelayBuilder;
use crate::build::traits::components::chain_builder::ChainBuilder;
use crate::build::traits::components::relay_from_chains_builder::RelayFromChainsBuilder;
use crate::build::traits::target::chain::{ChainATarget, ChainBTarget};
use crate::build::traits::target::relay::{RelayAToBTarget, RelayBToATarget};
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::components::default::build::DefaultBuildComponents;
use crate::core::traits::component::HasComponents;
use crate::core::traits::error::HasErrorType;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::two_way::HasTwoWayRelay;

pub trait UseDefaultBuilderComponents: CanBuildBiRelay {}

impl<Build, BiRelay, RelayAToB, RelayBToA, ChainA, ChainB, BaseComponents>
    UseDefaultBuilderComponents for Build
where
    Build: HasErrorType
        + HasBiRelayType<BiRelay = BiRelay>
        + HasRelayCache<RelayAToBTarget>
        + HasRelayCache<RelayBToATarget>
        + HasChainCache<ChainATarget>
        + HasChainCache<ChainBTarget>
        + HasComponents<Components = DefaultBuildComponents<BaseComponents>>,
    BiRelay: HasTwoWayRelay<RelayAToB = RelayAToB, RelayBToA = RelayBToA>,
    RelayAToB: Clone + HasRelayChains<SrcChain = ChainA, DstChain = ChainB>,
    RelayBToA: Clone + HasRelayChains<SrcChain = ChainB, DstChain = ChainA>,
    ChainA: Clone + HasIbcChainTypes<ChainB>,
    ChainB: Clone + HasIbcChainTypes<ChainA>,
    ChainA::ChainId: Ord + Clone,
    ChainB::ChainId: Ord + Clone,
    ChainA::ClientId: Ord + Clone,
    ChainB::ClientId: Ord + Clone,
    BaseComponents: BiRelayFromRelayBuilder<Build>
        + RelayFromChainsBuilder<Build, RelayAToBTarget>
        + RelayFromChainsBuilder<Build, RelayBToATarget>
        + ChainBuilder<Build, ChainATarget>
        + ChainBuilder<Build, ChainBTarget>,
{
}

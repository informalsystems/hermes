use core::marker::PhantomData;

use crate::builder::components::birelay::BuildBiRelayFromRelays;
use crate::builder::components::chain::cache::BuildChainWithCache;
use crate::builder::components::relay::build_from_chain::BuildRelayFromChains;
use crate::builder::components::relay::cache::BuildRelayWithCache;
use crate::builder::traits::birelay::build::BiRelayBuilderComponent;
use crate::builder::traits::birelay::from_relays::BiRelayFromRelayBuilderComponent;
use crate::builder::traits::chain::ChainBuilderComponent;
use crate::builder::traits::relay::build::RelayBuilderComponent;
use crate::builder::traits::relay::from_chains::RelayFromChainsBuilderComponent;
pub struct DefaultBuildComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_component!(
    ChainBuilderComponent,
    DefaultBuildComponents<BaseComponents>,
    BuildChainWithCache<BaseComponents>,
);

crate::delegate_component!(
    RelayBuilderComponent,
    DefaultBuildComponents<BaseComponents>,
    BuildRelayWithCache<BuildRelayFromChains>,
);

crate::delegate_component!(
    BiRelayBuilderComponent,
    DefaultBuildComponents<BaseComponents>,
    BuildBiRelayFromRelays,
);

crate::delegate_components!(
    [
        RelayFromChainsBuilderComponent,
        BiRelayFromRelayBuilderComponent,
    ],
    DefaultBuildComponents<BaseComponents>,
    BaseComponents,
);

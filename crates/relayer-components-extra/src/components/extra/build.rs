use core::marker::PhantomData;

use ibc_relayer_components::builder::components::relay::build_from_chain::BuildRelayFromChains;
use ibc_relayer_components::builder::components::relay::cache::BuildRelayWithCache;
use ibc_relayer_components::builder::traits::chain::ChainBuilderComponent;
use ibc_relayer_components::builder::traits::relay::RelayBuilderComponent;
use ibc_relayer_components::components::default::build::DefaultBuildComponents;

use crate::builder::impls::batch::BuildBatchWorker;

pub struct ExtraBuildComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_component!(
    RelayBuilderComponent,
    ExtraBuildComponents<BaseComponents>,
    BuildRelayWithCache<BuildRelayFromChains<BuildBatchWorker<BaseComponents>>>,
);

ibc_relayer_components::delegate_components!(
    [ChainBuilderComponent,],
    ExtraBuildComponents<BaseComponents>,
    DefaultBuildComponents<BaseComponents>,
);

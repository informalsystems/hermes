use core::marker::PhantomData;

use ibc_relayer_components::builder::traits::birelay::build::BiRelayBuilderComponent;
use ibc_relayer_components::builder::traits::chain::ChainBuilderComponent;
use ibc_relayer_components::builder::traits::relay::build::RelayBuilderComponent;
use ibc_relayer_components::builder::traits::relay::from_chains::RelayFromChainsBuilderComponent;
use ibc_relayer_components::components::default::build::DefaultBuildComponents;

use crate::builder::components::relay::batch::BuildRelayWithBatchWorker;
use crate::builder::traits::relay::RelayWithBatchBuilderComponent;

pub struct ExtraBuildComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_component!(
    RelayFromChainsBuilderComponent,
    ExtraBuildComponents<BaseComponents>,
    BuildRelayWithBatchWorker,
);

ibc_relayer_components::delegate_component!(
    RelayWithBatchBuilderComponent,
    ExtraBuildComponents<BaseComponents>,
    BaseComponents,
);

ibc_relayer_components::delegate_components!(
    [
        ChainBuilderComponent,
        RelayBuilderComponent,
        BiRelayBuilderComponent,
    ],
    ExtraBuildComponents<BaseComponents>,
    DefaultBuildComponents<BaseComponents>,
);

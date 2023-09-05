use core::marker::PhantomData;

use ibc_relayer_components::builder::traits::components::birelay_builder::BiRelayBuilderComponent;
use ibc_relayer_components::builder::traits::components::birelay_from_relay_builder::BiRelayFromRelayBuilderComponent;
use ibc_relayer_components::builder::traits::components::chain_builder::ChainBuilderComponent;
use ibc_relayer_components::builder::traits::components::relay_builder::RelayBuilderComponent;
use ibc_relayer_components::builder::traits::components::relay_from_chains_builder::RelayFromChainsBuilderComponent;
use ibc_relayer_components::components::default::build::DefaultBuildComponents;

use crate::builder::components::relay::batch::BuildRelayWithBatchWorker;
use crate::builder::traits::components::relay_with_batch_builder::RelayWithBatchBuilderComponent;

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
        BiRelayFromRelayBuilderComponent,
    ],
    ExtraBuildComponents<BaseComponents>,
    DefaultBuildComponents<BaseComponents>,
);

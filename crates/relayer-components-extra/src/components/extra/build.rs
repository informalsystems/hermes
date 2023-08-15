use core::marker::PhantomData;

use ibc_relayer_components::builder::traits::chain::ChainBuilderComponent;
use ibc_relayer_components::builder::traits::relay::build::RelayBuilderComponent;
use ibc_relayer_components::builder::traits::relay::from_chains::RelayFromChainsBuilderComponent;
use ibc_relayer_components::components::default::build::DefaultBuildComponents;

use crate::builder::impls::batch::BuildBatchWorker;
use crate::builder::traits::relay::RelayWithBatchBuilderComponent;

pub struct ExtraBuildComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_component!(
    RelayFromChainsBuilderComponent,
    ExtraBuildComponents<BaseComponents>,
    BuildBatchWorker,
);

ibc_relayer_components::delegate_component!(
    RelayWithBatchBuilderComponent,
    ExtraBuildComponents<BaseComponents>,
    BaseComponents,
);

ibc_relayer_components::delegate_components!(
    [ChainBuilderComponent, RelayBuilderComponent,],
    ExtraBuildComponents<BaseComponents>,
    DefaultBuildComponents<BaseComponents>,
);

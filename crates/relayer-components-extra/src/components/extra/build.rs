use core::marker::PhantomData;

use ibc_relayer_components::builder::traits::chain::ChainBuilderComponent;
use ibc_relayer_components::components::default::build::DefaultBuildComponents;

pub struct ExtraBuildComponents<BaseComponents>(pub PhantomData<BaseComponents>);

ibc_relayer_components::delegate_components!(
    [ChainBuilderComponent,],
    ExtraBuildComponents<BaseComponents>,
    DefaultBuildComponents<BaseComponents>,
);

use core::marker::PhantomData;

use crate::builder::components::chain::cache::BuildChainWithCache;
use crate::builder::traits::chain::ChainBuilderComponent;
pub struct DefaultBuildComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_component!(
    ChainBuilderComponent,
    DefaultBuildComponents<BaseComponents>,
    BuildChainWithCache<BaseComponents>,
);

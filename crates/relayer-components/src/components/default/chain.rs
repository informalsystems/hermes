use core::marker::PhantomData;

use crate::chain::traits::queries::consensus_state::ConsensusStateQuerierComponent;
use crate::chain::traits::queries::status::ChainStatusQuerierComponent;
pub struct DefaultChainComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_component!(
    ChainStatusQuerierComponent,
    DefaultChainComponents<BaseComponents>,
    BaseComponents,
);

crate::delegate_component!(
    ConsensusStateQuerierComponent,
    DefaultChainComponents<BaseComponents>,
    BaseComponents
);

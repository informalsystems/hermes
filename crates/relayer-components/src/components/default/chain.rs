use core::marker::PhantomData;

use crate::chain::traits::components::chain_status_querier::ChainStatusQuerierComponent;
use crate::chain::traits::components::consensus_state_querier::ConsensusStateQuerierComponent;
use crate::chain::traits::components::message_sender::MessageSenderComponent;
pub struct DefaultChainComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_components!(
    [
        ChainStatusQuerierComponent,
        ConsensusStateQuerierComponent,
        MessageSenderComponent,
    ],
    DefaultChainComponents<BaseComponents>,
    BaseComponents,
);

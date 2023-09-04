use core::marker::PhantomData;

use crate::chain::traits::components::message_sender::MessageSenderComponent;
use crate::chain::traits::queries::consensus_state::ConsensusStateQuerierComponent;
use crate::chain::traits::queries::status::ChainStatusQuerierComponent;
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

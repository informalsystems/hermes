use core::marker::PhantomData;

use crate::chain::traits::components::chain_status_querier::ChainStatusQuerierComponent;
use crate::chain::traits::components::consensus_state_querier::ConsensusStateQuerierComponent;
use crate::chain::traits::components::message_sender::MessageSenderComponent;
use crate::chain::traits::components::packet_fields_reader::PacketFieldsReaderComponent;
pub struct DefaultChainComponents<BaseComponents>(pub PhantomData<BaseComponents>);

crate::delegate_components!(
    [
        ChainStatusQuerierComponent,
        ConsensusStateQuerierComponent,
        MessageSenderComponent,
        PacketFieldsReaderComponent,
    ],
    DefaultChainComponents<BaseComponents>,
    BaseComponents,
);

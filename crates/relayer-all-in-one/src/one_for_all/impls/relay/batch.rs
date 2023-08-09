use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components_extra::batch::traits::channel::HasMessageBatchSender;
use ibc_relayer_components_extra::batch::types::aliases::MessageBatchSender;

use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;

impl<Relay> HasMessageBatchSender<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error> {
        self.relay.src_chain_message_batch_sender()
    }
}

impl<Relay> HasMessageBatchSender<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error> {
        self.relay.dst_chain_message_batch_sender()
    }
}

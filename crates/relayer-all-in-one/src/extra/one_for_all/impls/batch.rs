use async_trait::async_trait;
use ibc_relayer_components::chain::types::aliases::{Event, Message};
use ibc_relayer_components::relay::traits::ibc_message_sender::IbcMessageSender;
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};
use ibc_relayer_components_extra::batch::traits::channel::HasMessageBatchSender;
use ibc_relayer_components_extra::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use ibc_relayer_components_extra::batch::types::aliases::MessageBatchSender;

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::extra::one_for_all::presets::full::IbcMessageSenderForBatchWorker;
use crate::extra::one_for_all::traits::relay::OfaFullRelay;
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Target> CanSendIbcMessagesFromBatchWorker<Target> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    Target: ChainTarget<Self>,
    IbcMessageSenderForBatchWorker: IbcMessageSender<Self, Target>,
{
    async fn send_messages_from_batch_worker(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error> {
        IbcMessageSenderForBatchWorker::send_messages(self, messages).await
    }
}

impl<Relay> HasMessageBatchSender<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaFullRelay,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error> {
        self.relay.src_chain_message_batch_sender()
    }
}

impl<Relay> HasMessageBatchSender<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaFullRelay,
{
    fn get_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error> {
        self.relay.dst_chain_message_batch_sender()
    }
}

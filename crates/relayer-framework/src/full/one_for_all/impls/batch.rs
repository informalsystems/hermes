use async_trait::async_trait;

use crate::base::chain::types::aliases::{Event, Message};
use crate::base::core::traits::error::HasErrorType;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::impls::message_senders::chain_sender::SendIbcMessagesToChain;
use crate::base::relay::impls::message_senders::update_client::SendIbcMessagesWithUpdateClient;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::full::batch::context::{BatchChannel, BatchContext, HasBatchContext};
use crate::full::batch::message_sender::CanSendIbcMessagesFromBatchWorker;
use crate::full::one_for_all::traits::batch::{OfaBatch, OfaBatchWrapper};
use crate::full::one_for_all::traits::chain::OfaFullChain;
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Target> CanSendIbcMessagesFromBatchWorker<Target> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    Target: ChainTarget<Self>,
    SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>: IbcMessageSender<Self, Target>,
{
    async fn send_messages_from_batch_worker(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error> {
        <SendIbcMessagesWithUpdateClient<SendIbcMessagesToChain>>::send_messages(self, messages)
            .await
    }
}

impl<Chain, Batch> HasErrorType for OfaBatchWrapper<Chain>
where
    Chain: OfaFullChain<BatchContext = Batch>,
    Batch: OfaBatch<Chain>,
{
    type Error = Chain::Error;
}

#[async_trait]
impl<Chain, Batch> BatchContext for OfaBatchWrapper<Chain>
where
    Chain: OfaFullChain<BatchContext = Batch>,
    Batch: OfaBatch<Chain>,
{
    type Message = Chain::Message;

    type Event = Chain::Event;

    type BatchSender = Batch::BatchSender;

    type BatchReceiver = Batch::BatchReceiver;

    type ResultSender = Batch::ResultSender;

    type ResultReceiver = Batch::ResultReceiver;

    fn new_batch_channel() -> (Self::BatchSender, Self::BatchReceiver) {
        Batch::new_batch_channel()
    }

    fn new_result_channel() -> (Self::ResultSender, Self::ResultReceiver) {
        Batch::new_result_channel()
    }

    fn send_batch(
        sender: &Self::BatchSender,
        messages: Vec<Self::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Self::Error> {
        Batch::send_batch(sender, messages, result_sender)
    }

    async fn try_receive_batch(
        receiver: &Self::BatchReceiver,
    ) -> Result<Option<(Vec<Self::Message>, Self::ResultSender)>, Self::Error> {
        let result = Batch::try_receive_batch(receiver).await?;

        Ok(result)
    }

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Self::Event>>, Self::Error>, Self::Error> {
        Batch::receive_result(result_receiver).await
    }

    fn send_result(
        result_sender: Self::ResultSender,
        result: Result<Vec<Vec<Chain::Event>>, Self::Error>,
    ) -> Result<(), Self::Error> {
        Batch::send_result(result_sender, result)
    }
}

impl<Relay> HasBatchContext<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    // TODO: do not require the chain error to be the same as relay error.
    // this can be fixed in #2816.
    Relay::SrcChain: OfaFullChain<Error = Relay::Error>,
{
    type BatchContext = OfaBatchWrapper<Relay::SrcChain>;

    fn batch_channel(
        &self,
    ) -> &BatchChannel<
        <Self::BatchContext as BatchContext>::BatchSender,
        <Self::BatchContext as BatchContext>::BatchReceiver,
    > {
        self.relay.src_chain().chain.batch_channel()
    }
}

impl<Relay> HasBatchContext<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    Relay::DstChain: OfaFullChain<Error = Relay::Error>,
{
    type BatchContext = OfaBatchWrapper<Relay::DstChain>;

    fn batch_channel(
        &self,
    ) -> &BatchChannel<
        <Self::BatchContext as BatchContext>::BatchSender,
        <Self::BatchContext as BatchContext>::BatchReceiver,
    > {
        self.relay.dst_chain().chain.batch_channel()
    }
}

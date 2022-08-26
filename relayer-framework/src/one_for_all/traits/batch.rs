use async_trait::async_trait;
use core::marker::PhantomData;

use crate::addons::batch::context::{BatchContext, HasBatchContext};
use crate::core::traits::core::Async;
use crate::core::traits::target::{DestinationTarget, SourceTarget};
use crate::one_for_all::impls::message::OfaMessage;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::error::OfaErrorContext;
use crate::one_for_all::traits::relay::{OfaRelay, OfaRelayContext};
use crate::std_prelude::*;

#[derive(Clone)]
pub struct OfaBatchContext<Chain> {
    pub phantom: PhantomData<Chain>,
}

#[async_trait]
pub trait OfaBatch<Chain: OfaChain>: Async {
    type MessagesSender: Async;
    type MessagesReceiver: Async;

    type ResultSender: Async;
    type ResultReceiver: Async;

    fn new_result_channel() -> (Self::ResultSender, Self::ResultReceiver);

    async fn send_messages(
        sender: &Self::MessagesSender,
        messages: Vec<Chain::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Chain::Error>;

    async fn try_receive_messages(
        receiver: &mut Self::MessagesReceiver,
    ) -> Result<Option<(Vec<Chain::Message>, Self::ResultSender)>, Chain::Error>;

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Chain::Event>>, Chain::Error>, Chain::Error>;

    fn send_result(
        result_sender: Self::ResultSender,
        events: Result<Vec<Vec<Chain::Event>>, Chain::Error>,
    ) -> Result<(), Chain::Error>;
}

pub trait OfaChainWithBatch: OfaChain {
    type BatchContext: OfaBatch<Self>;

    fn batch_sender(&self) -> &<Self::BatchContext as OfaBatch<Self>>::MessagesSender;
}

#[async_trait]
impl<Chain, Batch> BatchContext for OfaBatchContext<Chain>
where
    Chain: OfaChainWithBatch<BatchContext = Batch>,
    Batch: OfaBatch<Chain>,
{
    type Error = OfaErrorContext<Chain::Error>;

    type Message = OfaMessage<Chain>;

    type Event = Chain::Event;

    type MessagesSender = Batch::MessagesSender;

    type MessagesReceiver = Batch::MessagesReceiver;

    type ResultSender = Batch::ResultSender;

    type ResultReceiver = Batch::ResultReceiver;

    fn new_result_channel() -> (Self::ResultSender, Self::ResultReceiver) {
        Batch::new_result_channel()
    }

    async fn send_messages(
        sender: &Self::MessagesSender,
        messages: Vec<Self::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Self::Error> {
        let in_messages = messages
            .into_iter()
            .map(|message| message.message)
            .collect();
        Batch::send_messages(sender, in_messages, result_sender)
            .await
            .map_err(OfaErrorContext::new)
    }

    async fn try_receive_messages(
        receiver: &mut Self::MessagesReceiver,
    ) -> Result<Option<(Vec<Self::Message>, Self::ResultSender)>, Self::Error> {
        let result = Batch::try_receive_messages(receiver)
            .await
            .map_err(OfaErrorContext::new)?;

        match result {
            Some((messages, result_sender)) => Ok(Some((
                messages.into_iter().map(OfaMessage::new).collect(),
                result_sender,
            ))),
            None => Ok(None),
        }
    }

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Self::Event>>, Self::Error>, Self::Error> {
        let result = Batch::receive_result(result_receiver).await;

        match result {
            Ok(Ok(events)) => Ok(Ok(events)),
            Ok(Err(e)) => Ok(Err(OfaErrorContext::new(e))),
            Err(e) => Err(OfaErrorContext::new(e)),
        }
    }

    fn send_result(
        result_sender: Self::ResultSender,
        result: Result<Vec<Vec<Chain::Event>>, Self::Error>,
    ) -> Result<(), Self::Error> {
        let in_result = result.map_err(|e| e.error);

        Batch::send_result(result_sender, in_result).map_err(OfaErrorContext::new)
    }
}

impl<Relay> HasBatchContext<SourceTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay,
    Relay::SrcChain: OfaChainWithBatch,
{
    type BatchContext = OfaBatchContext<Relay::SrcChain>;

    fn messages_sender(&self) -> &<Self::BatchContext as BatchContext>::MessagesSender {
        self.relay.src_chain().chain.batch_sender()
    }
}

impl<Relay> HasBatchContext<DestinationTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay,
    Relay::DstChain: OfaChainWithBatch,
{
    type BatchContext = OfaBatchContext<Relay::DstChain>;

    fn messages_sender(&self) -> &<Self::BatchContext as BatchContext>::MessagesSender {
        self.relay.dst_chain().chain.batch_sender()
    }
}

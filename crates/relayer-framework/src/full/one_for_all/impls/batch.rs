use async_trait::async_trait;

use crate::base::one_for_all::traits::error::OfaErrorContext;
use crate::base::one_for_all::traits::relay::{OfaRelay, OfaRelayWrapper};
use crate::base::traits::target::{DestinationTarget, SourceTarget};
use crate::full::batch::context::{BatchChannel, BatchContext, HasBatchContext};
use crate::full::one_for_all::traits::batch::{OfaBatch, OfaBatchContext};
use crate::full::one_for_all::traits::chain::OfaFullChain;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Batch> BatchContext for OfaBatchContext<Chain>
where
    Chain: OfaFullChain<BatchContext = Batch>,
    Batch: OfaBatch<Chain>,
{
    type Error = OfaErrorContext<Chain::Error>;

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

    async fn send_batch(
        sender: &Self::BatchSender,
        messages: Vec<Self::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Self::Error> {
        Batch::send_batch(sender, messages, result_sender)
            .await
            .map_err(OfaErrorContext::new)
    }

    async fn try_receive_batch(
        receiver: &Self::BatchReceiver,
    ) -> Result<Option<(Vec<Self::Message>, Self::ResultSender)>, Self::Error> {
        let result = Batch::try_receive_batch(receiver)
            .await
            .map_err(OfaErrorContext::new)?;

        Ok(result)
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

impl<Relay> HasBatchContext<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
    Relay::SrcChain: OfaFullChain,
{
    type BatchContext = OfaBatchContext<Relay::SrcChain>;

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
    Relay: OfaRelay,
    Relay::DstChain: OfaFullChain,
{
    type BatchContext = OfaBatchContext<Relay::DstChain>;

    fn batch_channel(
        &self,
    ) -> &BatchChannel<
        <Self::BatchContext as BatchContext>::BatchSender,
        <Self::BatchContext as BatchContext>::BatchReceiver,
    > {
        self.relay.dst_chain().chain.batch_channel()
    }
}

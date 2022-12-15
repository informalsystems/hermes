use async_trait::async_trait;

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::full::one_for_all::types::runtime::aliases::{MessageBatchReceiver, MessageBatchSender};
use crate::std_prelude::*;

#[async_trait]
pub trait OfaFullRelay: OfaBaseRelay {
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;

    fn is_retryable_error(e: &Self::Error) -> bool;

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error;

    fn src_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::SrcChain, Self::Error>;

    fn src_chain_message_batch_receiver(
        &self,
    ) -> &MessageBatchReceiver<Self::SrcChain, Self::Error>;

    fn dst_chain_message_batch_sender(&self) -> &MessageBatchSender<Self::DstChain, Self::Error>;

    fn dst_chain_message_batch_receiver(
        &self,
    ) -> &MessageBatchReceiver<Self::DstChain, Self::Error>;
}

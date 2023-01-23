use alloc::sync::Arc;
use async_trait::async_trait;
use ibc_relayer_framework::full::one_for_all::traits::relay::OfaFullRelay;

use crate::base::error::Error;
use crate::base::types::relay::CosmosRelayWrapper;
use crate::full::traits::relay::CosmosFullRelay;
use crate::full::types::batch::{CosmosBatchReceiver, CosmosBatchSender};

#[async_trait]
impl<Relay> OfaFullRelay for CosmosRelayWrapper<Relay>
where
    Relay: CosmosFullRelay,
{
    fn from_shared_error(e: Arc<Error>) -> Error {
        Error::shared(e)
    }

    fn is_retryable_error(_: &Error) -> bool {
        false
    }

    fn max_retry_exceeded_error(e: Error) -> Error {
        e
    }

    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Ok(self
            .relay
            .packet_filter()
            .is_allowed(&packet.source_port, &packet.source_channel))
    }

    fn src_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        self.relay.src_chain_message_batch_sender()
    }

    fn src_chain_message_batch_receiver(&self) -> &CosmosBatchReceiver {
        self.relay.src_chain_message_batch_receiver()
    }

    fn dst_chain_message_batch_sender(&self) -> &CosmosBatchSender {
        self.relay.dst_chain_message_batch_sender()
    }

    fn dst_chain_message_batch_receiver(&self) -> &CosmosBatchReceiver {
        self.relay.dst_chain_message_batch_receiver()
    }
}

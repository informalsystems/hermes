use async_trait::async_trait;
use ibc_relayer_framework::full::one_for_all::traits::relay::OfaFullRelay;

use crate::base::types::relay::CosmosRelayWrapper;
use crate::full::traits::relay::CosmosFullRelay;

#[async_trait]
impl<Relay> OfaFullRelay for CosmosRelayWrapper<Relay>
where
    Relay: CosmosFullRelay,
{
    fn is_retryable_error(_: &Self::Error) -> bool {
        false
    }

    fn max_retry_exceeded_error(e: Self::Error) -> Self::Error {
        e
    }

    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Ok(self
            .relay
            .packet_filter()
            .is_allowed(&packet.source_port, &packet.source_channel))
    }
}

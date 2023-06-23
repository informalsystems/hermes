use async_trait::async_trait;
use ibc_relayer_components::relay::traits::packet_relayers::lock::HasPacketLock;

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> HasPacketLock for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
{
    type PacketLock<'a> = Relay::PacketLock<'a>;

    async fn try_acquire_packet_lock<'a>(
        &'a self,
        packet: &'a Self::Packet,
    ) -> Option<Self::PacketLock<'a>> {
        self.relay.try_acquire_packet_lock(packet).await
    }
}

use async_trait::async_trait;

use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::impls::packet_relayers::general::full_relay::FullRelayer;
use crate::base::relay::impls::packet_relayers::general::retry::RetryRelayer;
use crate::base::relay::traits::packet_relayer::{CanRelayPacket, PacketRelayer};
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanRelayPacket for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    RetryRelayer<FullRelayer>: PacketRelayer<Self>,
{
    async fn relay_packet(&self, packet: &Self::Packet) -> Result<(), Self::Error> {
        <RetryRelayer<FullRelayer>>::relay_packet(self, packet).await
    }
}

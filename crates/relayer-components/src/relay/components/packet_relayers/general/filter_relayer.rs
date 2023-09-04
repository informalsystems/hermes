use core::marker::PhantomData;

use async_trait::async_trait;

use crate::relay::traits::components::packet_filter::CanFilterPackets;
use crate::relay::traits::components::packet_relayer::PacketRelayer;
use crate::std_prelude::*;

pub struct FilterRelayer<InRelayer> {
    pub phantom: PhantomData<InRelayer>,
}

#[async_trait]
impl<Relay, InRelayer> PacketRelayer<Relay> for FilterRelayer<InRelayer>
where
    Relay: CanFilterPackets,
    InRelayer: PacketRelayer<Relay>,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error> {
        if relay.should_relay_packet(packet).await? {
            InRelayer::relay_packet(relay, packet).await
        } else {
            Ok(())
        }
    }
}

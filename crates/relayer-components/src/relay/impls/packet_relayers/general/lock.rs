use core::marker::PhantomData;

use async_trait::async_trait;

use crate::relay::traits::packet_relayer::PacketRelayer;
use crate::relay::traits::packet_relayers::lock::HasPacketLock;
use crate::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct LockPacketRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer> PacketRelayer<Relay> for LockPacketRelayer<InRelayer>
where
    Relay: HasRelayTypes + HasPacketLock,
    InRelayer: PacketRelayer<Relay>,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error> {
        let m_lock = relay.try_acquire_packet_lock(packet).await;

        match m_lock {
            Some(_lock) => InRelayer::relay_packet(relay, packet).await,
            None => Ok(()),
        }
    }
}

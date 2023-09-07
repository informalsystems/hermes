use core::marker::PhantomData;

use async_trait::async_trait;

use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::packet_relayer::PacketRelayer;
use crate::relay::traits::logs::logger::CanLogRelay;
use crate::relay::traits::logs::packet::CanLogRelayPacket;
use crate::relay::traits::packet_lock::HasPacketLock;
use crate::std_prelude::*;

/**
   Call the inner relayer only if the packet lock provided by [`HasPacketLock`]
   is acquired.

   This is to avoid race condition where multiple packet relayers try to
   relay the same packet at the same time.
*/
pub struct LockPacketRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer> PacketRelayer<Relay> for LockPacketRelayer<InRelayer>
where
    Relay: HasRelayChains + HasPacketLock + CanLogRelay + CanLogRelayPacket,
    InRelayer: PacketRelayer<Relay>,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error> {
        let m_lock = relay.try_acquire_packet_lock(packet).await;

        match m_lock {
            Some(_lock) => InRelayer::relay_packet(relay, packet).await,
            None => {
                relay.log_relay(
                    Relay::Logger::LEVEL_TRACE,
                    "skip relaying packet, as another packet relayer has acquired the packet lock",
                    |log| {
                        log.field("packet", Relay::log_packet(packet));
                    },
                );

                Ok(())
            }
        }
    }
}

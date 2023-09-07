use core::marker::PhantomData;

use async_trait::async_trait;

use crate::logger::traits::level::HasBaseLogLevels;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::packet_relayer::PacketRelayer;
use crate::relay::traits::logs::logger::CanLogRelay;
use crate::relay::traits::logs::packet::CanLogRelayPacket;
use crate::std_prelude::*;

pub struct LoggerRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer> PacketRelayer<Relay> for LoggerRelayer<InRelayer>
where
    Relay: HasRelayChains + CanLogRelay + CanLogRelayPacket,
    InRelayer: PacketRelayer<Relay>,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error> {
        relay.log_relay(Default::default(), "starting to relay packet", |log| {
            log.field("packet", Relay::log_packet(packet));
        });

        let res = InRelayer::relay_packet(relay, packet).await;

        if let Err(e) = &res {
            relay.log_relay(
                Relay::Logger::LEVEL_ERROR,
                "failed to relay packet",
                |log| {
                    log.field("packet", Relay::log_packet(packet))
                        .debug("error", e);
                },
            );
        } else {
            relay.log_relay(Default::default(), "successfully relayed packet", |log| {
                log.field("packet", Relay::log_packet(packet));
            });
        }

        res
    }
}

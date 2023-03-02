use core::marker::PhantomData;

use async_trait::async_trait;

use crate::logger::traits::level::HasBaseLogLevels;
use crate::logger::traits::log::CanLog;
use crate::relay::traits::logs::packet::CanLogRelayPacket;
use crate::relay::traits::packet_relayer::PacketRelayer;
use crate::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct LoggerRelayer<InRelayer>(pub PhantomData<InRelayer>);

#[async_trait]
impl<Relay, InRelayer> PacketRelayer<Relay> for LoggerRelayer<InRelayer>
where
    Relay: HasRelayTypes + CanLog + CanLogRelayPacket,
    InRelayer: PacketRelayer<Relay>,
{
    async fn relay_packet(relay: &Relay, packet: &Relay::Packet) -> Result<(), Relay::Error> {
        relay.log(Default::default(), "starting to relay packet", |log| {
            log.field("packet", Relay::log_packet(packet));
        });

        let res = InRelayer::relay_packet(relay, packet).await;

        if let Err(e) = &res {
            relay.log(
                Relay::Logger::LEVEL_ERROR,
                "failed to relay packet",
                |log| {
                    log.field("packet", Relay::log_packet(packet))
                        .debug("error", e);
                },
            );
        } else {
            relay.log(Default::default(), "successfully relayed packet", |log| {
                log.field("packet", Relay::log_packet(packet));
            });
        }

        res
    }
}

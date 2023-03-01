use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;

pub trait CanLogChainPacket<Counterparty>: HasLoggerType + HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcPacketTypes<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    fn log_outgoing_packet<'a>(
        packet: &'a Self::OutgoingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;

    fn log_incoming_packet<'a>(
        packet: &'a Self::IncomingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}

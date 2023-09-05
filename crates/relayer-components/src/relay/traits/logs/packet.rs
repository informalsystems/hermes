use crate::chain::traits::logs::packet::CanLogChainPacket;
use crate::logger::traits::has_logger::HasLoggerType;
use crate::logger::traits::logger::BaseLogger;
use crate::relay::traits::chains::HasRelayChains;

pub trait CanLogRelayPacket: HasRelayChains + HasLoggerType {
    fn log_packet<'a>(packet: &'a Self::Packet) -> <Self::Logger as BaseLogger>::LogValue<'a>;
}

impl<Relay, Logger> CanLogRelayPacket for Relay
where
    Logger: BaseLogger,
    Relay: HasRelayChains + HasLoggerType<Logger = Logger>,
    Relay::SrcChain: CanLogChainPacket<Relay::DstChain, Logger = Logger>,
{
    fn log_packet<'a>(packet: &'a Self::Packet) -> Logger::LogValue<'a> {
        Relay::SrcChain::log_outgoing_packet(packet)
    }
}

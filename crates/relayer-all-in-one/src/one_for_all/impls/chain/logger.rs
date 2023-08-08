use ibc_relayer_components::chain::traits::logs::event::CanLogChainEvent;
use ibc_relayer_components::chain::traits::logs::packet::CanLogChainPacket;
use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::logger::traits::logger::BaseLogger;

use crate::one_for_all::traits::chain::{OfaChain, OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;

impl<Chain> HasLoggerType for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    type Logger = Chain::Logger;
}

impl<Chain> HasLogger for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    fn logger(&self) -> &Self::Logger {
        self.chain.logger()
    }
}

impl<Chain> CanLogChainEvent for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    fn log_event<'a>(event: &'a Chain::Event) -> <Chain::Logger as BaseLogger>::LogValue<'a> {
        Chain::log_event(event)
    }
}

impl<Chain, Counterparty> CanLogChainPacket<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    fn log_incoming_packet<'a>(
        packet: &'a Self::IncomingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        Chain::log_incoming_packet(packet)
    }

    fn log_outgoing_packet<'a>(
        packet: &'a Self::OutgoingPacket,
    ) -> <Self::Logger as BaseLogger>::LogValue<'a> {
        Chain::log_outgoing_packet(packet)
    }
}

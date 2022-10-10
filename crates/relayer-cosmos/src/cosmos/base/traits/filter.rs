use ibc_relayer_framework::base::traits::core::Async;
use ibc_relayer_types::core::ics04_channel::packet::Packet;

pub trait CosmosFilter: Async {
    fn should_relay_packet(&self, packet: &Packet) -> bool;
}

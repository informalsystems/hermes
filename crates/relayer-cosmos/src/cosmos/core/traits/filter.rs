use ibc::core::ics04_channel::packet::Packet;
use ibc_relayer_framework::core::traits::core::Async;
pub trait CosmosFilter: Async {
    fn should_relay_packet(&self, packet: &Packet) -> bool;
}

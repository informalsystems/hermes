use crate::core::traits::contexts::relay::RelayContext;

pub trait FilterContext: RelayContext {
    fn should_relay(&self, packet: &Self::Packet) -> bool;
}

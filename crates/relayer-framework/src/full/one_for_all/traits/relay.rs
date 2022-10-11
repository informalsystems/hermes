use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::std_prelude::*;
use async_trait::async_trait;

#[async_trait]
pub trait OfaFullRelay: OfaBaseRelay {
    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error>;
}

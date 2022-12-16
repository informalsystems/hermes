use async_trait::async_trait;

use crate::base::chain::traits::types::HasIbcPacketTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildReceivePacketMessage<Counterparty>: HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcPacketTypes<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    async fn build_receive_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::OutgoingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;
}

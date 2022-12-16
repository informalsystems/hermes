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

#[async_trait]
pub trait ReceivePacketMessageBuilder<Chain, Counterparty>
where
    Chain: HasIbcPacketTypes<Counterparty>,
    Counterparty: HasIbcPacketTypes<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    async fn build_receive_packet_message(
        chain: &Chain,
        height: &Chain::Height,
        packet: &Chain::OutgoingPacket,
    ) -> Result<Counterparty::Message, Chain::Error>;
}

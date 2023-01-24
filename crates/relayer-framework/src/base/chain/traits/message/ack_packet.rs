use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::types::HasIbcPacketTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildAckPacketMessage<Counterparty>:
    HasWriteAcknowledgementEvent<Counterparty> + HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcPacketTypes<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    async fn build_ack_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Counterparty::Message, Self::Error>;
}

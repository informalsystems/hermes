use async_trait::async_trait;

use crate::base::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::types::packet::HasIbcPacketTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryWriteAck<Counterparty>: HasWriteAcknowledgementEvent<Counterparty>
where
    Counterparty: HasIbcPacketTypes<
        Self,
        IncomingPacket = Self::OutgoingPacket,
        OutgoingPacket = Self::IncomingPacket,
    >,
{
    async fn query_write_ack_event(
        &self,
        packet: &Self::IncomingPacket,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error>;
}

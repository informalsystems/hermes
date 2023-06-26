use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryWriteAcknowledgement<Counterparty>:
    HasWriteAcknowledgementEvent<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_write_acknowledgement_event(
        &self,
        packet: &Self::IncomingPacket,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error>;
}

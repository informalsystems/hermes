use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasWriteAcknowledgementEvent;
use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryWriteAck<Counterparty>: HasWriteAcknowledgementEvent<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_write_ack_event(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequence: &Counterparty::Sequence,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error>;
}

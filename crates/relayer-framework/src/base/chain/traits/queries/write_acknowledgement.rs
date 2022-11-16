use async_trait::async_trait;

use crate::base::chain::traits::ibc_event::HasIbcEvents;
use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::std_prelude::*;

// #[async_trait]
// pub trait WriteAckQuerier<Chain, Counterparty>
// where
//     Chain: HasIbcChainTypes<Counterparty>,
//     Counterparty: HasIbcChainTypes<Chain>,
// {
//     async fn query_write_ack_event(
//         channel_id: &Chain::ChannelId,
//         port_id: &Chain::PortId,
//         counterparty_channel_id: &Counterparty::ChannelId,
//         counterparty_port_id: &Counterparty::PortId,
//     ) -> Result<Option<Chain::WriteAcknowledgementEvent>, Chain::Error>;
// }

#[async_trait]
pub trait CanQueryWriteAck<Counterparty>: HasIbcEvents<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_write_ack_event(
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequence: &Counterparty::Sequence,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error>;
}

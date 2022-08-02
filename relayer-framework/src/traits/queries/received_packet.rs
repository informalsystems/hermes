use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::chain_context::IbcChainContext;

#[async_trait]
pub trait ReceivedPacketQuerier<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: IbcChainContext<Self>,
{
    async fn is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error>;
}

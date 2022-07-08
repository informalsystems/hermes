use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::chain_context::IbcChainContext;
use crate::types::aliases::{ChannelId, PortId, Sequence};

#[async_trait]
pub trait ReceivedPacketQuerier<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: IbcChainContext<Self>,
{
    async fn is_packet_received(
        &self,
        port_id: &PortId<Self, Counterparty>,
        channel_id: &ChannelId<Self, Counterparty>,
        sequence: &Sequence<Counterparty, Self>,
    ) -> Result<bool, Self::Error>;
}

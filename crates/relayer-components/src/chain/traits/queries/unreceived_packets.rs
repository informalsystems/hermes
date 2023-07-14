use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::send_packet::HasSendPacketEvent;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait UnreceivedPacketSequencesQuerier<Chain, Counterparty>
where
    Chain: HasIbcPacketTypes<Counterparty> + HasErrorType,
    Counterparty: HasIbcChainTypes<Chain>,
{
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &Chain::ChannelId,
        port_id: &Chain::PortId,
        sequences: &[Counterparty::Sequence],
    ) -> Result<(Vec<Chain::Sequence>, Chain::Height), Chain::Error>;
}

#[async_trait]
pub trait CanQueryUnreceivedPacketSequences<Counterparty>:
    HasIbcPacketTypes<Counterparty> + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_unreceived_packet_sequences(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        sequences: &[Counterparty::Sequence],
    ) -> Result<(Vec<Self::Sequence>, Self::Height), Self::Error>;
}

#[async_trait]
pub trait UnreceivedPacketEventsQuerier<Chain, Counterparty>
where
    Chain: HasIbcPacketTypes<Counterparty> + HasSendPacketEvent<Counterparty> + HasErrorType,
    Counterparty: HasIbcChainTypes<Chain>,
{
    async fn query_unreceived_packet_events(
        &self,
        channel_id: &Chain::ChannelId,
        port_id: &Chain::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Chain::Sequence],
        height: &Chain::Height,
    ) -> Result<Vec<Chain::Event>, Chain::Error>;
}

#[async_trait]
pub trait CanQueryUnreceivedPacketEvents<Counterparty>:
    HasIbcPacketTypes<Counterparty> + HasSendPacketEvent<Counterparty> + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn query_unreceived_packet_events(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Self::Sequence],
        height: &Self::Height,
    ) -> Result<Vec<Self::SendPacketEvent>, Self::Error>;
}

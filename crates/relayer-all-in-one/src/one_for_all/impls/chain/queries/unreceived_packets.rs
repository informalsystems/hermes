use async_trait::async_trait;

use ibc_relayer_components::chain::traits::queries::unreceived_packets::CanQueryUnreceivedPackets;

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> CanQueryUnreceivedPackets<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty> + OfaChainTypes,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_unreceived_packets(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequences: &[Counterparty::Sequence],
    ) -> Result<Vec<Self::OutgoingPacket>, Self::Error> {
        let unreceived_packet = self
            .chain
            .query_unreceived_packets(
                channel_id,
                port_id,
                counterparty_channel_id,
                counterparty_port_id,
                sequences,
            )
            .await?;
        Ok(unreceived_packet)
    }
}

use async_trait::async_trait;

use crate::one_for_all::traits::chain::OfaIbcChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;
use ibc_relayer_components::chain::traits::queries::received_packet::CanQueryReceivedPacket;

#[async_trait]
impl<Chain, Counterparty> CanQueryReceivedPacket<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    async fn query_is_packet_received(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        sequence: &Counterparty::Sequence,
    ) -> Result<bool, Self::Error> {
        let is_received = self
            .chain
            .is_packet_received(port_id, channel_id, sequence)
            .await?;

        Ok(is_received)
    }
}

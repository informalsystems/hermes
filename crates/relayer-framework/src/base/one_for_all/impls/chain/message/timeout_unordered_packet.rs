use async_trait::async_trait;

use crate::base::chain::traits::message::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage;
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> CanBuildTimeoutUnorderedPacketMessage<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Counterparty::Message, Self::Error> {
        self.chain
            .build_timeout_unordered_packet_message(height, packet)
            .await
    }
}

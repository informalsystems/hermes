use async_trait::async_trait;

use crate::base::chain::traits::queries::write_ack::CanQueryWriteAck;
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::base::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Chain, Counterparty> CanQueryWriteAck<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<
        Chain,
        IncomingPacket = Chain::OutgoingPacket,
        OutgoingPacket = Chain::IncomingPacket,
    >,
{
    async fn query_write_ack_event(
        &self,
        packet: &Self::IncomingPacket,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error> {
        self.chain.query_write_ack_event(packet).await
    }
}

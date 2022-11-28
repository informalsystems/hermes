use async_trait::async_trait;

use crate::base::chain::traits::queries::write_acknowledgement::CanQueryWriteAck;
use crate::base::one_for_all::traits::chain::OfaIbcChain;
use crate::std_prelude::*;

#[derive(Clone)]
pub struct OfaChainWrapper<Chain> {
    pub chain: Chain,
}

impl<Chain> OfaChainWrapper<Chain> {
    pub fn new(chain: Chain) -> Self {
        Self { chain }
    }
}

#[async_trait]
impl<Chain, Counterparty> CanQueryWriteAck<OfaChainWrapper<Counterparty>> for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn query_write_ack_event(
        &self,
        channel_id: &Self::ChannelId,
        port_id: &Self::PortId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_port_id: &Counterparty::PortId,
        sequence: &Counterparty::Sequence,
    ) -> Result<Option<Self::WriteAcknowledgementEvent>, Self::Error> {
        let can_query_write_ack = self
            .chain
            .query_write_ack_event(
                channel_id,
                port_id,
                counterparty_channel_id,
                counterparty_port_id,
                sequence,
            )
            .await?;

        Ok(can_query_write_ack)
    }
}

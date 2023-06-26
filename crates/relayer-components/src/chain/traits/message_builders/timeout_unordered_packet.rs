use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildTimeoutUnorderedPacketMessage<Counterparty>:
    HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;
}

use async_trait::async_trait;

use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildReceivePacketMessage<Counterparty>: HasIbcPacketTypes<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_receive_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::OutgoingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;
}

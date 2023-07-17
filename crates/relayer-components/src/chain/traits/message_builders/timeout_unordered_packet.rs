use async_trait::async_trait;

use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::chain::traits::types::packets::timeout::HasTimeoutUnorderedPacketPayload;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildTimeoutUnorderedPacketPayload<Counterparty>:
    HasTimeoutUnorderedPacketPayload<Counterparty>
    + HasIbcPacketTypes<Counterparty>
    + HasHeightType
    + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Self::TimeoutUnorderedPacketPayload, Self::Error>;
}

#[async_trait]
pub trait CanBuildTimeoutUnorderedPacketMessage<Counterparty>:
    HasIbcPacketTypes<Counterparty> + HasHeightType + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Counterparty::Message, Self::Error>;
}

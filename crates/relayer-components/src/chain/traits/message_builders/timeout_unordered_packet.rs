use async_trait::async_trait;

use crate::chain::traits::types::client_state::HasClientStateType;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::message::HasMessageType;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::chain::traits::types::packets::timeout::HasTimeoutUnorderedPacketPayload;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildTimeoutUnorderedPacketPayload<Counterparty>:
    HasTimeoutUnorderedPacketPayload<Counterparty>
    + HasIbcPacketTypes<Counterparty>
    + HasClientStateType<Counterparty>
    + HasHeightType
    + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_timeout_unordered_packet_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Self::TimeoutUnorderedPacketPayload, Self::Error>;
}

#[async_trait]
pub trait CanBuildTimeoutUnorderedPacketMessage<Counterparty>:
    HasMessageType + HasErrorType
where
    Counterparty: HasTimeoutUnorderedPacketPayload<Self>,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        payload: Counterparty::TimeoutUnorderedPacketPayload,
    ) -> Result<Self::Message, Self::Error>;
}

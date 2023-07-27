use async_trait::async_trait;

use crate::chain::traits::types::client_state::HasClientStateType;
use crate::chain::traits::types::height::HasHeightType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent;
use crate::chain::traits::types::message::HasMessageType;
use crate::chain::traits::types::packet::HasIbcPacketTypes;
use crate::chain::traits::types::packets::ack::HasAckPacketPayload;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildAckPacketPayload<Counterparty>:
    HasAckPacketPayload<Counterparty>
    + HasWriteAcknowledgementEvent<Counterparty>
    + HasIbcPacketTypes<Counterparty>
    + HasClientStateType<Counterparty>
    + HasHeightType
    + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_ack_packet_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
        ack: &Self::WriteAcknowledgementEvent,
    ) -> Result<Self::AckPacketPayload, Self::Error>;
}

#[async_trait]
pub trait CanBuildAckPacketMessage<Counterparty>: HasMessageType + HasErrorType
where
    Counterparty: HasAckPacketPayload<Self>,
{
    async fn build_ack_packet_message(
        &self,
        payload: Counterparty::AckPacketPayload,
    ) -> Result<Self::Message, Self::Error>;
}

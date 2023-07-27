use async_trait::async_trait;
use ibc_relayer_components::chain::traits::message_builders::timeout_unordered_packet::{
    CanBuildTimeoutUnorderedPacketMessage, CanBuildTimeoutUnorderedPacketPayload,
};
use ibc_relayer_components::chain::traits::types::packets::timeout::HasTimeoutUnorderedPacketPayload;

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasTimeoutUnorderedPacketPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type TimeoutUnorderedPacketPayload = Chain::TimeoutUnorderedPacketPayload;
}

#[async_trait]
impl<Chain, Counterparty> CanBuildTimeoutUnorderedPacketPayload<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_timeout_unordered_packet_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        packet: &Self::IncomingPacket,
    ) -> Result<Self::TimeoutUnorderedPacketPayload, Self::Error> {
        self.chain
            .build_timeout_unordered_packet_payload(client_state, height, packet)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildTimeoutUnorderedPacketMessage<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_timeout_unordered_packet_message(
        &self,
        payload: Counterparty::TimeoutUnorderedPacketPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_timeout_unordered_packet_message(payload)
            .await
    }
}

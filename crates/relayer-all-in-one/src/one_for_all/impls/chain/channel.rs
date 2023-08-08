use async_trait::async_trait;

use ibc_relayer_components::chain::traits::message_builders::channel::{
    CanBuildChannelHandshakeMessages, CanBuildChannelHandshakePayloads,
};
use ibc_relayer_components::chain::traits::types::channel::{
    HasChannelHandshakePayloads, HasInitChannelOptionsType,
};
use ibc_relayer_components::chain::traits::types::ibc_events::channel::{
    HasChannelOpenInitEvent, HasChannelOpenTryEvent,
};

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasChannelHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type ChannelOpenTryPayload = Chain::ChannelOpenTryPayload;

    type ChannelOpenAckPayload = Chain::ChannelOpenAckPayload;

    type ChannelOpenConfirmPayload = Chain::ChannelOpenConfirmPayload;
}

impl<Chain, Counterparty> HasInitChannelOptionsType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type InitChannelOptions = Chain::InitChannelOptions;
}

impl<Chain, Counterparty> HasChannelOpenInitEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    type ChannelOpenInitEvent = Chain::ChannelOpenInitEvent;

    fn try_extract_channel_open_init_event(
        event: Chain::Event,
    ) -> Option<Chain::ChannelOpenInitEvent> {
        Chain::try_extract_channel_open_init_event(event)
    }

    fn channel_open_init_event_channel_id(
        event: &Chain::ChannelOpenInitEvent,
    ) -> &Chain::ChannelId {
        Chain::channel_open_init_event_channel_id(event)
    }
}

impl<Chain, Counterparty> HasChannelOpenTryEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    type ChannelOpenTryEvent = Chain::ChannelOpenTryEvent;

    fn try_extract_channel_open_try_event(
        event: Chain::Event,
    ) -> Option<Chain::ChannelOpenTryEvent> {
        Chain::try_extract_channel_open_try_event(event)
    }

    fn channel_open_try_event_channel_id(event: &Chain::ChannelOpenTryEvent) -> &Chain::ChannelId {
        Chain::channel_open_try_event_channel_id(event)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildChannelHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_channel_open_try_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenTryPayload, Self::Error> {
        self.chain
            .build_channel_open_try_payload(client_state, height, port_id, channel_id)
            .await
    }

    async fn build_channel_open_ack_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenAckPayload, Self::Error> {
        self.chain
            .build_channel_open_ack_payload(client_state, height, port_id, channel_id)
            .await
    }

    async fn build_channel_open_confirm_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenConfirmPayload, Self::Error> {
        self.chain
            .build_channel_open_confirm_payload(client_state, height, port_id, channel_id)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildChannelHandshakeMessages<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_channel_open_init_message(
        &self,
        port_id: &Self::PortId,
        counterparty_port_id: &Counterparty::PortId,
        init_channel_options: &Self::InitChannelOptions,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_channel_open_init_message(port_id, counterparty_port_id, init_channel_options)
            .await
    }

    async fn build_channel_open_try_message(
        &self,
        dst_port_id: &Self::PortId,
        src_port_id: &Counterparty::PortId,
        src_channel_id: &Counterparty::ChannelId,
        counterparty_payload: Counterparty::ChannelOpenTryPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_channel_open_try_message(
                dst_port_id,
                src_port_id,
                src_channel_id,
                counterparty_payload,
            )
            .await
    }

    async fn build_channel_open_ack_message(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        counterparty_channel_id: &Counterparty::ChannelId,
        counterparty_payload: Counterparty::ChannelOpenAckPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_channel_open_ack_message(
                port_id,
                channel_id,
                counterparty_channel_id,
                counterparty_payload,
            )
            .await
    }

    async fn build_channel_open_confirm_message(
        &self,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
        counterparty_payload: Counterparty::ChannelOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_channel_open_confirm_message(port_id, channel_id, counterparty_payload)
            .await
    }
}

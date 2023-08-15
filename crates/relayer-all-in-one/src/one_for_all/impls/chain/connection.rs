use async_trait::async_trait;
use ibc_relayer_components::chain::traits::message_builders::connection::{
    CanBuildConnectionHandshakeMessages, CanBuildConnectionHandshakePayloads,
};
use ibc_relayer_components::chain::traits::types::connection::{
    HasConnectionHandshakePayloads, HasInitConnectionOptionsType,
};
use ibc_relayer_components::chain::traits::types::ibc_events::connection::{
    HasConnectionOpenInitEvent, HasConnectionOpenTryEvent,
};

use crate::one_for_all::traits::chain::{OfaChainTypes, OfaIbcChain};
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasConnectionHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type ConnectionOpenInitPayload = Chain::ConnectionOpenInitPayload;

    type ConnectionOpenTryPayload = Chain::ConnectionOpenTryPayload;

    type ConnectionOpenAckPayload = Chain::ConnectionOpenAckPayload;

    type ConnectionOpenConfirmPayload = Chain::ConnectionOpenConfirmPayload;
}

impl<Chain, Counterparty> HasInitConnectionOptionsType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaChainTypes,
    Counterparty: OfaChainTypes,
{
    type InitConnectionOptions = Chain::InitConnectionOptions;
}

impl<Chain, Counterparty> HasConnectionOpenInitEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    type ConnectionOpenInitEvent = Chain::ConnectionOpenInitEvent;

    fn try_extract_connection_open_init_event(
        event: Chain::Event,
    ) -> Option<Chain::ConnectionOpenInitEvent> {
        Chain::try_extract_connection_open_init_event(event)
    }

    fn connection_open_init_event_connection_id(
        event: &Chain::ConnectionOpenInitEvent,
    ) -> &Chain::ConnectionId {
        Chain::connection_open_init_event_connection_id(event)
    }
}

impl<Chain, Counterparty> HasConnectionOpenTryEvent<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    type ConnectionOpenTryEvent = Chain::ConnectionOpenTryEvent;

    fn try_extract_connection_open_try_event(
        event: Chain::Event,
    ) -> Option<Chain::ConnectionOpenTryEvent> {
        Chain::try_extract_connection_open_try_event(event)
    }

    fn connection_open_try_event_connection_id(
        event: &Chain::ConnectionOpenTryEvent,
    ) -> &Chain::ConnectionId {
        Chain::connection_open_try_event_connection_id(event)
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildConnectionHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_connection_open_init_payload(
        &self,
        client_state: &Self::ClientState,
    ) -> Result<Self::ConnectionOpenInitPayload, Self::Error> {
        self.chain
            .build_connection_open_init_payload(client_state)
            .await
    }

    async fn build_connection_open_try_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Self::Error> {
        self.chain
            .build_connection_open_try_payload(client_state, height, client_id, connection_id)
            .await
    }

    async fn build_connection_open_ack_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Self::Error> {
        self.chain
            .build_connection_open_ack_payload(client_state, height, client_id, connection_id)
            .await
    }

    async fn build_connection_open_confirm_payload(
        &self,
        client_state: &Self::ClientState,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Self::Error> {
        self.chain
            .build_connection_open_confirm_payload(client_state, height, client_id, connection_id)
            .await
    }
}

#[async_trait]
impl<Chain, Counterparty> CanBuildConnectionHandshakeMessages<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaChainTypes,
{
    async fn build_connection_open_init_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        init_connection_options: &Self::InitConnectionOptions,
        counterparty_payload: Counterparty::ConnectionOpenInitPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_init_message(
                client_id,
                counterparty_client_id,
                init_connection_options,
                counterparty_payload,
            )
            .await
    }

    async fn build_connection_open_try_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenTryPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_try_message(
                client_id,
                counterparty_client_id,
                counterparty_connection_id,
                counterparty_payload,
            )
            .await
    }

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenAckPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_ack_message(
                connection_id,
                counterparty_connection_id,
                counterparty_payload,
            )
            .await
    }

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error> {
        self.chain
            .build_connection_open_confirm_message(connection_id, counterparty_payload)
            .await
    }
}

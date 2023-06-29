use async_trait::async_trait;
use ibc_relayer_components::chain::traits::message_builders::connection::CanBuildConnectionHandshakePayloads;
use ibc_relayer_components::chain::traits::types::connection::{
    HasConnectionDetailsType, HasConnectionHandshakePayloads, HasConnectionVersionType,
    HasInitConnectionOptionsType,
};

use crate::one_for_all::traits::chain::OfaIbcChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use crate::std_prelude::*;

impl<Chain, Counterparty> HasConnectionHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConnectionOpenInitPayload = Chain::ConnectionOpenInitPayload;

    type ConnectionOpenTryPayload = Chain::ConnectionOpenTryPayload;

    type ConnectionOpenAckPayload = Chain::ConnectionOpenAckPayload;

    type ConnectionOpenConfirmPayload = Chain::ConnectionOpenConfirmPayload;
}

impl<Chain, Counterparty> HasInitConnectionOptionsType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type InitConnectionOptions = Chain::InitConnectionOptions;
}

impl<Chain, Counterparty> HasConnectionVersionType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConnectionVersion = Chain::ConnectionVersion;
}

impl<Chain, Counterparty> HasConnectionDetailsType<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    type ConnectionDetails = Chain::ConnectionDetails;
}

#[async_trait]
impl<Chain, Counterparty> CanBuildConnectionHandshakePayloads<OfaChainWrapper<Counterparty>>
    for OfaChainWrapper<Chain>
where
    Chain: OfaIbcChain<Counterparty>,
    Counterparty: OfaIbcChain<Chain>,
{
    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<Self::ConnectionOpenInitPayload, Self::Error> {
        self.chain.build_connection_open_init_payload().await
    }

    async fn build_connection_open_try_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Self::Error> {
        self.chain
            .build_connection_open_try_payload(height, client_id, connection_id)
            .await
    }

    async fn build_connection_open_ack_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Self::Error> {
        self.chain
            .build_connection_open_ack_payload(height, client_id, connection_id)
            .await
    }

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Self::Error> {
        self.chain
            .build_connection_open_confirm_payload(height, client_id, connection_id)
            .await
    }
}

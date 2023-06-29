use core::time::Duration;

use async_trait::async_trait;

use crate::chain::traits::types::connection::{
    HasConnectionHandshakePayloads, HasConnectionVersionType,
};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildConnectionHandshakePayloads<Counterparty>:
    HasConnectionHandshakePayloads<Counterparty> + HasErrorType
{
    async fn build_connection_open_init_payload(
        &self,
    ) -> Result<Self::ConnectionInitPayload, Self::Error>;

    async fn build_connection_open_try_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenTryPayload, Self::Error>;

    async fn build_connection_open_ack_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenAckPayload, Self::Error>;

    async fn build_connection_open_confirm_payload(
        &self,
        height: &Self::Height,
        client_id: &Self::ClientId,
        connection_id: &Self::ConnectionId,
    ) -> Result<Self::ConnectionOpenConfirmPayload, Self::Error>;
}

#[async_trait]
pub trait CanBuildConnectionHandshakeMessages<Counterparty>:
    HasConnectionVersionType<Counterparty> + HasErrorType
where
    Counterparty: HasConnectionHandshakePayloads<Self>,
{
    async fn build_connection_open_init_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        connection_version: &Self::ConnectionVersion,
        delay_period: Duration,
        counterparty_payload: Counterparty::ConnectionInitPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_connection_open_try_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_payload: Counterparty::ConnectionOpenTryPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_connection_open_ack_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenAckPayload,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_payload: Counterparty::ConnectionOpenConfirmPayload,
    ) -> Result<Self::Message, Self::Error>;
}

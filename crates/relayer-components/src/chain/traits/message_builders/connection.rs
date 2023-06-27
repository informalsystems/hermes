use core::time::Duration;

use async_trait::async_trait;

use crate::chain::traits::types::client_state::HasClientStateType;
use crate::chain::traits::types::commitment::{HasCommitmentPrefixType, HasCommitmentProofsType};
use crate::chain::traits::types::connection::HasConnectionVersionType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::chain::traits::types::message::HasMessageType;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildConnectionOpenInitMessage<Counterparty>:
    HasIbcChainTypes<Counterparty>
    + HasConnectionVersionType<Counterparty>
    + HasMessageType
    + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>,
{
    async fn build_connection_open_init_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        connection_version: &Self::ConnectionVersion,
        delay_period: Duration,
    ) -> Result<Self::Message, Self::Error>;
}

#[async_trait]
pub trait CanBuildConnectionOpenTryMessage<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasMessageType + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self>
        + HasConnectionVersionType<Self>
        + HasCommitmentPrefixType<Self>
        + HasCommitmentProofsType<Self>,
{
    async fn build_connection_open_try_message(
        &self,
        client_id: &Self::ClientId,
        counterparty_client_id: &Counterparty::ClientId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        counterparty_commitment: &Counterparty::CommitmentPrefix,
        connection_version: &Counterparty::ConnectionVersion,
        commitment_proofs: &Counterparty::CommitmentProofs,
        delay_period: Duration,
    ) -> Result<Self::Message, Self::Error>;
}

#[async_trait]
pub trait CanBuildConnectionOpenAckMessage<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasClientStateType<Counterparty> + HasMessageType + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self> + HasCommitmentProofsType<Self>,
{
    async fn build_connection_open_ack_message(
        &self,
        connection_id: &Self::ConnectionId,
        counterparty_connection_id: &Counterparty::ConnectionId,
        client_state: &Self::ClientState,
        commitment_proofs: &Counterparty::CommitmentProofs,
    ) -> Result<Self::Message, Self::Error>;
}

#[async_trait]
pub trait CanBuildConnectionOpenConfirmMessage<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasMessageType + HasErrorType
where
    Counterparty: HasIbcChainTypes<Self> + HasCommitmentProofsType<Self>,
{
    async fn build_connection_open_confirm_message(
        &self,
        connection_id: &Self::ConnectionId,
        commitment_proofs: &Counterparty::CommitmentProofs,
    ) -> Result<Self::Message, Self::Error>;
}

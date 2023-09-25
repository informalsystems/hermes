use alloc::sync::Arc;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryConnectionRequest, QueryHeight};
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::connection::ConnectionMsgType;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId};
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::methods::runtime::HasBlockingChainHandle;
use crate::traits::message::{CosmosMessage, ToCosmosMessage};
use crate::types::connection::CosmosInitConnectionOptions;
use crate::types::error::{BaseError, Error};
use crate::types::messages::connection::open_ack::CosmosConnectionOpenAckMessage;
use crate::types::messages::connection::open_confirm::CosmosConnectionOpenConfirmMessage;
use crate::types::messages::connection::open_init::CosmosConnectionOpenInitMessage;
use crate::types::messages::connection::open_try::CosmosConnectionOpenTryMessage;
use crate::types::payloads::connection::{
    CosmosConnectionOpenAckPayload, CosmosConnectionOpenConfirmPayload,
    CosmosConnectionOpenInitPayload, CosmosConnectionOpenTryPayload,
};

pub async fn build_connection_open_init_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
) -> Result<CosmosConnectionOpenInitPayload, Error> {
    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let commitment_prefix = chain_handle
                .query_commitment_prefix()
                .map_err(BaseError::relayer)?;

            Ok(CosmosConnectionOpenInitPayload { commitment_prefix })
        })
        .await
}

pub async fn build_connection_open_try_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    client_id: &ClientId,
    connection_id: &ConnectionId,
) -> Result<CosmosConnectionOpenTryPayload, Error> {
    let height = *height;
    let client_id = client_id.clone();
    let connection_id = connection_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let commitment_prefix = chain_handle
                .query_commitment_prefix()
                .map_err(BaseError::relayer)?;

            let (connection, _) = chain_handle
                .query_connection(
                    QueryConnectionRequest {
                        connection_id: connection_id.clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map_err(BaseError::relayer)?;

            let versions = connection.versions().to_vec();
            let delay_period = connection.delay_period();

            let (m_client_state, proofs) = chain_handle
                .build_connection_proofs_and_client_state(
                    ConnectionMsgType::OpenTry,
                    &connection_id,
                    &client_id,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let any_client_state = m_client_state
                .ok_or_else(|| BaseError::generic(eyre!("expect some client state")))?;

            let client_state = match any_client_state {
                AnyClientState::Tendermint(client_state) => client_state,
                _ => return Err(BaseError::generic(eyre!("expect tendermint client state")).into()),
            };

            let proof_client = proofs
                .client_proof()
                .clone()
                .ok_or_else(|| BaseError::generic(eyre!("expect non empty client proof")))?
                .clone();

            let proof_consensus = proofs
                .consensus_proof()
                .ok_or_else(|| BaseError::generic(eyre!("expect non empty consensus proof")))?
                .clone();

            let payload = CosmosConnectionOpenTryPayload {
                commitment_prefix,
                client_state,
                versions,
                delay_period,
                update_height: proofs.height(),
                proof_init: proofs.object_proof().clone(),
                proof_client,
                proof_consensus,
            };

            Ok(payload)
        })
        .await
}

pub async fn build_connection_open_ack_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    client_id: &ClientId,
    connection_id: &ConnectionId,
) -> Result<CosmosConnectionOpenAckPayload, Error> {
    let height = *height;
    let client_id = client_id.clone();
    let connection_id = connection_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let (connection, _) = chain_handle
                .query_connection(
                    QueryConnectionRequest {
                        connection_id: connection_id.clone(),
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map_err(BaseError::relayer)?;

            let version = connection
                .versions()
                .iter()
                .next()
                .cloned()
                .unwrap_or_default();

            let (m_client_state, proofs) = chain_handle
                .build_connection_proofs_and_client_state(
                    ConnectionMsgType::OpenAck,
                    &connection_id,
                    &client_id,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let any_client_state = m_client_state
                .ok_or_else(|| BaseError::generic(eyre!("expect some client state")))?;

            let client_state = match any_client_state {
                AnyClientState::Tendermint(client_state) => client_state,
                _ => return Err(BaseError::generic(eyre!("expect tendermint client state")).into()),
            };

            let proof_client = proofs
                .client_proof()
                .clone()
                .ok_or_else(|| BaseError::generic(eyre!("expect non empty client proof")))?
                .clone();

            let proof_consensus = proofs
                .consensus_proof()
                .ok_or_else(|| BaseError::generic(eyre!("expect non empty consensus proof")))?
                .clone();

            let payload = CosmosConnectionOpenAckPayload {
                client_state,
                version,
                update_height: proofs.height(),
                proof_try: proofs.object_proof().clone(),
                proof_client,
                proof_consensus,
            };

            Ok(payload)
        })
        .await
}

pub async fn build_connection_open_confirm_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    height: &Height,
    client_id: &ClientId,
    connection_id: &ConnectionId,
) -> Result<CosmosConnectionOpenConfirmPayload, Error> {
    let height = *height;
    let client_id = client_id.clone();
    let connection_id = connection_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let (_, proofs) = chain_handle
                .build_connection_proofs_and_client_state(
                    ConnectionMsgType::OpenConfirm,
                    &connection_id,
                    &client_id,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let update_height = proofs.height();
            let proof_ack = proofs.object_proof().clone();

            let payload = CosmosConnectionOpenConfirmPayload {
                update_height,
                proof_ack,
            };

            Ok(payload)
        })
        .await
}

pub async fn build_connection_open_init_message<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    client_id: &ClientId,
    counterparty_client_id: &ClientId,
    init_connection_options: &CosmosInitConnectionOptions,
    counterparty_payload: CosmosConnectionOpenInitPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let client_id = client_id.clone();
    let counterparty_client_id = counterparty_client_id.clone();
    let counterparty_commitment_prefix = counterparty_payload.commitment_prefix;
    let delay_period = init_connection_options.delay_period;

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let versions = chain_handle
                .query_compatible_versions()
                .map_err(BaseError::relayer)?;

            let version = versions.into_iter().next().unwrap_or_default();

            let message = CosmosConnectionOpenInitMessage {
                client_id,
                counterparty_client_id,
                counterparty_commitment_prefix,
                version,
                delay_period,
            };

            Ok(message.to_cosmos_message())
        })
        .await
}

pub fn build_connection_open_try_message(
    client_id: &ClientId,
    counterparty_client_id: &ClientId,
    counterparty_connection_id: &ConnectionId,
    counterparty_payload: CosmosConnectionOpenTryPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let message = CosmosConnectionOpenTryMessage {
        client_id: client_id.clone(),
        counterparty_client_id: counterparty_client_id.clone(),
        counterparty_connection_id: counterparty_connection_id.clone(),
        counterparty_commitment_prefix: counterparty_payload.commitment_prefix.clone(),
        counterparty_versions: counterparty_payload.versions,
        delay_period: counterparty_payload.delay_period,
        client_state: counterparty_payload.client_state.into(),
        update_height: counterparty_payload.update_height,
        proof_init: counterparty_payload.proof_init,
        proof_client: counterparty_payload.proof_client,
        proof_consensus: counterparty_payload.proof_consensus,
    };

    Ok(message.to_cosmos_message())
}

pub fn build_connection_open_ack_message(
    connection_id: &ConnectionId,
    counterparty_connection_id: &ConnectionId,
    counterparty_payload: CosmosConnectionOpenAckPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let connection_id = connection_id.clone();
    let counterparty_connection_id = counterparty_connection_id.clone();

    let message = CosmosConnectionOpenAckMessage {
        connection_id,
        counterparty_connection_id,
        version: counterparty_payload.version,
        client_state: counterparty_payload.client_state.into(),
        update_height: counterparty_payload.update_height,
        proof_try: counterparty_payload.proof_try,
        proof_client: counterparty_payload.proof_client,
        proof_consensus: counterparty_payload.proof_consensus,
    };

    Ok(message.to_cosmos_message())
}

pub fn build_connection_open_confirm_message(
    connection_id: &ConnectionId,
    counterparty_payload: CosmosConnectionOpenConfirmPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let message = CosmosConnectionOpenConfirmMessage {
        connection_id: connection_id.clone(),
        update_height: counterparty_payload.update_height,
        proof_ack: counterparty_payload.proof_ack,
    };

    Ok(message.to_cosmos_message())
}

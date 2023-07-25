use alloc::sync::Arc;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryConnectionRequest, QueryHeight};
use ibc_relayer::connection::ConnectionMsgType;
use ibc_relayer_types::core::ics03_connection::connection::Counterparty as ConnectionCounterparty;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc_relayer_types::core::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc_relayer_types::core::ics03_connection::version::Version as ConnectionVersion;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId};
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::methods::runtime::HasBlockingChainHandle;
use crate::traits::message::{wrap_cosmos_message, AsCosmosMessage, CosmosMessage};
use crate::types::connection::{
    CosmosConnectionOpenAckPayload, CosmosConnectionOpenConfirmPayload,
    CosmosConnectionOpenInitPayload, CosmosConnectionOpenTryPayload, CosmosInitConnectionOptions,
};
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;
use crate::types::messages::connection_open_init::CosmosConnectionOpenInitMessage;

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

            let (client_state, proofs) = chain_handle
                .build_connection_proofs_and_client_state(
                    ConnectionMsgType::OpenTry,
                    &connection_id,
                    &client_id,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let payload = CosmosConnectionOpenTryPayload {
                commitment_prefix,
                proofs,
                client_state,
                versions,
                delay_period,
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

            let (client_state, proofs) = chain_handle
                .build_connection_proofs_and_client_state(
                    ConnectionMsgType::OpenAck,
                    &connection_id,
                    &client_id,
                    height,
                )
                .map_err(BaseError::relayer)?;

            let payload = CosmosConnectionOpenAckPayload {
                proofs,
                client_state,
                version,
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

            let payload = CosmosConnectionOpenConfirmPayload { proofs };

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

            Ok(message.as_cosmos_message())
        })
        .await
}

pub fn build_connection_open_try_message(
    client_id: &ClientId,
    counterparty_client_id: &ClientId,
    counterparty_connection_id: &ConnectionId,
    counterparty_payload: CosmosConnectionOpenTryPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let client_id = client_id.clone();
    let counterparty = ConnectionCounterparty::new(
        counterparty_client_id.clone(),
        Some(counterparty_connection_id.clone()),
        counterparty_payload.commitment_prefix.clone(),
    );

    let message = CosmosIbcMessage::new(None, move |signer| {
        let client_state = counterparty_payload.client_state.clone().map(Into::into);
        let counterparty_versions: Vec<ConnectionVersion> = counterparty_payload.versions.clone();
        let proofs = counterparty_payload.proofs.clone();
        let delay_period = counterparty_payload.delay_period;
        let counterparty = counterparty.clone();

        let message = MsgConnectionOpenTry {
            client_id: client_id.clone(),
            client_state,
            counterparty,
            counterparty_versions,
            delay_period,
            proofs,
            signer: signer.clone(),
            previous_connection_id: None, // deprecated
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
}

pub fn build_connection_open_ack_message(
    connection_id: &ConnectionId,
    counterparty_connection_id: &ConnectionId,
    counterparty_payload: CosmosConnectionOpenAckPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let connection_id = connection_id.clone();
    let counterparty_connection_id = counterparty_connection_id.clone();

    let message = CosmosIbcMessage::new(None, move |signer| {
        let version = counterparty_payload.version.clone();
        let client_state = counterparty_payload.client_state.clone().map(Into::into);
        let proofs = counterparty_payload.proofs.clone();

        let message = MsgConnectionOpenAck {
            connection_id: connection_id.clone(),
            counterparty_connection_id: counterparty_connection_id.clone(),
            version,
            client_state,
            proofs,
            signer: signer.clone(),
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
}

pub fn build_connection_open_confirm_message(
    connection_id: &ConnectionId,
    counterparty_payload: CosmosConnectionOpenConfirmPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let connection_id = connection_id.clone();

    let message = CosmosIbcMessage::new(None, move |signer| {
        let proofs: ibc_relayer_types::proofs::Proofs = counterparty_payload.proofs.clone();

        let message = MsgConnectionOpenConfirm {
            connection_id: connection_id.clone(),
            proofs,
            signer: signer.clone(),
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
}

use alloc::sync::Arc;
use core::iter;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::light_client::AnyHeader;
use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::methods::runtime::HasBlockingChainHandle;
use crate::traits::message::{AsCosmosMessage, CosmosMessage};
use crate::types::client::CosmosUpdateClientPayload;
use crate::types::error::{BaseError, Error};
use crate::types::messages::update_client::CosmosUpdateClientMessage;

pub async fn build_update_client_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    trusted_height: &Height,
    target_height: &Height,
    client_state: ClientState,
) -> Result<CosmosUpdateClientPayload, Error> {
    let trusted_height = *trusted_height;
    let target_height = *target_height;

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let (header, support) = chain_handle
                .build_header(
                    trusted_height,
                    target_height,
                    AnyClientState::Tendermint(client_state),
                )
                .map_err(BaseError::relayer)?;

            let headers = iter::once(header)
                .chain(support.into_iter())
                .map(|header| match header {
                    AnyHeader::Tendermint(header) => Ok(header),
                    _ => Err(BaseError::generic(eyre!("expect tendermint header")).into()),
                })
                .collect::<Result<Vec<TendermintHeader>, Error>>()?;

            Ok(CosmosUpdateClientPayload { headers })
        })
        .await
}

pub fn build_update_client_message(
    client_id: &ClientId,
    payload: CosmosUpdateClientPayload,
) -> Result<Vec<Arc<dyn CosmosMessage>>, Error> {
    let messages = payload
        .headers
        .into_iter()
        .map(|header| {
            let message = CosmosUpdateClientMessage {
                client_id: client_id.clone(),
                header: header.into(),
            };

            message.as_cosmos_message()
        })
        .collect();

    Ok(messages)
}

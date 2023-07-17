use alloc::sync::Arc;
use core::iter;
use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::light_client::AnyHeader;
use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc_relayer_types::core::ics02_client::msgs::update_client::MsgUpdateClient;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::tx_msg::Msg;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::traits::message::{wrap_cosmos_message, CosmosMessage};
use crate::types::client::CosmosUpdateClientPayload;
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;

pub async fn build_update_client_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    trusted_height: &Height,
    target_height: &Height,
    client_state: ClientState,
) -> Result<CosmosUpdateClientPayload, Error> {
    let trusted_height = *trusted_height;
    let target_height = *target_height;
    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
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
        .map_err(BaseError::join)?
}

pub fn build_update_client_message(
    client_id: &ClientId,
    payload: CosmosUpdateClientPayload,
) -> Result<Vec<Arc<dyn CosmosMessage>>, Error> {
    let messages = payload
        .headers
        .into_iter()
        .map(|header| {
            let client_id = client_id.clone();
            let message = CosmosIbcMessage::new(None, move |signer| {
                let message = MsgUpdateClient {
                    client_id: client_id.clone(),
                    header: header.clone().into(),
                    signer: signer.clone(),
                };

                Ok(message.to_any())
            });

            wrap_cosmos_message(message)
        })
        .collect();

    Ok(messages)
}

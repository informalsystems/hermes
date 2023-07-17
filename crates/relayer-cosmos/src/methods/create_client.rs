use alloc::sync::Arc;
use eyre::eyre;
use ibc_relayer::chain::client::ClientSettings;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer_types::core::ics02_client::msgs::create_client::MsgCreateClient;
use ibc_relayer_types::tx_msg::Msg;

use crate::contexts::chain::CosmosChain;
use crate::traits::message::{wrap_cosmos_message, CosmosMessage};
use crate::types::client::CosmosCreateClientPayload;
use crate::types::error::{BaseError, Error};
use crate::types::message::CosmosIbcMessage;

pub async fn build_create_client_payload<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    client_settings: &ClientSettings,
) -> Result<CosmosCreateClientPayload, Error> {
    let client_settings = client_settings.clone();
    let chain_handle = chain.handle.clone();

    chain
        .runtime
        .runtime
        .runtime
        .spawn_blocking(move || {
            let height = chain_handle
                .query_latest_height()
                .map_err(BaseError::relayer)?;

            let any_client_state = chain_handle
                .build_client_state(height, client_settings)
                .map_err(BaseError::relayer)?;

            let client_state = match &any_client_state {
                AnyClientState::Tendermint(client_state) => client_state.clone(),
                _ => {
                    return Err(BaseError::generic(eyre!("expect Tendermint client state")).into());
                }
            };

            let any_consensus_state = chain_handle
                .build_consensus_state(any_client_state.latest_height(), height, any_client_state)
                .map_err(BaseError::relayer)?;

            let consensus_state = match any_consensus_state {
                AnyConsensusState::Tendermint(consensus_state) => consensus_state,
                _ => {
                    return Err(
                        BaseError::generic(eyre!("expect Tendermint consensus state")).into(),
                    );
                }
            };

            Ok(CosmosCreateClientPayload {
                client_state,
                consensus_state,
            })
        })
        .await
        .map_err(BaseError::join)?
}

pub fn build_create_client_message(
    payload: CosmosCreateClientPayload,
) -> Result<Arc<dyn CosmosMessage>, Error> {
    let message = CosmosIbcMessage::new(None, move |signer| {
        let message = MsgCreateClient {
            client_state: payload.client_state.clone().into(),
            consensus_state: payload.consensus_state.clone().into(),
            signer: signer.clone(),
        };

        Ok(message.to_any())
    });

    Ok(wrap_cosmos_message(message))
}

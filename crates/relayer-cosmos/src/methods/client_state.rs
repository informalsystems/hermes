use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryClientStateRequest, QueryHeight};
use ibc_relayer::client_state::AnyClientState;
use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;

use crate::contexts::chain::CosmosChain;
use crate::methods::runtime::HasBlockingChainHandle;
use crate::types::error::{BaseError, Error};

pub async fn query_client_state<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    client_id: &ClientId,
) -> Result<ClientState, Error> {
    let client_id = client_id.clone();

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let (client_state, _) = chain_handle
                .query_client_state(
                    QueryClientStateRequest {
                        client_id,
                        height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map_err(BaseError::relayer)?;

            match client_state {
                AnyClientState::Tendermint(client_state) => Ok(client_state),
                _ => Err(BaseError::generic(eyre!("expected tendermint client state")).into()),
            }
        })
        .await
}

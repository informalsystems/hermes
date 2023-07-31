use eyre::eyre;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{
    IncludeProof, PageRequest, QueryConsensusStateHeightsRequest, QueryConsensusStateRequest,
    QueryHeight,
};
use ibc_relayer::consensus_state::AnyConsensusState;
use ibc_relayer_types::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::Height;

use crate::contexts::chain::CosmosChain;
use crate::methods::runtime::HasBlockingChainHandle;
use crate::types::error::{BaseError, Error};

pub async fn query_consensus_state<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    client_id: &ClientId,
    height: &Height,
) -> Result<ConsensusState, Error> {
    let client_id = client_id.clone();
    let height = *height;

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let (any_consensus_state, _) = chain_handle
                .query_consensus_state(
                    QueryConsensusStateRequest {
                        client_id: client_id.clone(),
                        consensus_height: height,
                        query_height: QueryHeight::Latest,
                    },
                    IncludeProof::No,
                )
                .map_err(BaseError::relayer)?;

            match any_consensus_state {
                AnyConsensusState::Tendermint(consensus_state) => Ok(consensus_state),
                _ => Err(BaseError::mismatch_consensus_state().into()),
            }
        })
        .await
}

pub async fn find_consensus_state_height_before<Chain: ChainHandle>(
    chain: &CosmosChain<Chain>,
    client_id: &ClientId,
    target_height: &Height,
) -> Result<Height, Error> {
    let client_id = client_id.clone();
    let target_height = *target_height;

    chain
        .with_blocking_chain_handle(move |chain_handle| {
            let heights = {
                let mut heights = chain_handle
                    .query_consensus_state_heights(QueryConsensusStateHeightsRequest {
                        client_id,
                        pagination: Some(PageRequest::all()),
                    })
                    .map_err(BaseError::relayer)?;

                heights.sort_by_key(|&h| core::cmp::Reverse(h));

                heights
            };

            let height = heights
                .into_iter()
                .find(|height| height < &target_height)
                .ok_or_else(|| {
                    BaseError::generic(eyre!(
                        "no consensus state found that is smaller than target height {}",
                        target_height
                    ))
                })?;

            Ok(height)
        })
        .await
}

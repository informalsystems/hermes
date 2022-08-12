use async_trait::async_trait;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc::core::ics02_client::client_consensus::AnyConsensusState;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryConsensusStateRequest, QueryHeight};
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::queries::consensus_state::{
    CanQueryConsensusState, ConsensusStateQuerier, HasConsensusState,
};

use crate::cosmos::context::chain::CosmosChainContext;
use crate::cosmos::error::Error;

impl<Chain, Counterparty> HasConsensusState<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: Async,
    Counterparty: Async,
{
    type ConsensusState = ConsensusState;
}

pub struct CosmosConsensusStateQuerier;

#[async_trait]
impl<Chain, Counterparty>
    ConsensusStateQuerier<CosmosChainContext<Chain>, CosmosChainContext<Counterparty>>
    for CosmosConsensusStateQuerier
where
    Chain: ChainHandle,
    Counterparty: Async,
{
    async fn query_consensus_state(
        chain: &CosmosChainContext<Chain>,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<ConsensusState, Error> {
        let (any_consensus_state, _) = chain
            .handle
            .query_consensus_state(
                QueryConsensusStateRequest {
                    client_id: client_id.clone(),
                    consensus_height: *height,
                    query_height: QueryHeight::Latest,
                },
                IncludeProof::No,
            )
            .map_err(Error::relayer)?;

        match any_consensus_state {
            AnyConsensusState::Tendermint(consensus_state) => Ok(consensus_state),
            _ => Err(Error::mismatch_consensus_state()),
        }
    }
}

impl<Chain, Counterparty> CanQueryConsensusState<CosmosChainContext<Counterparty>>
    for CosmosChainContext<Chain>
where
    Chain: ChainHandle,
    Counterparty: Async,
{
    type ConsensusStateQuerier = CosmosConsensusStateQuerier;
}

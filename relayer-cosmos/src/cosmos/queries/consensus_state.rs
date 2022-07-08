use async_trait::async_trait;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState;
use ibc::core::ics02_client::client_consensus::AnyConsensusState;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::{IncludeProof, QueryConsensusStateRequest, QueryHeight};
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::queries::consensus_state::{
    ConsensusStateContext, ConsensusStateQuerier,
};

use crate::cosmos::error::Error;
use crate::cosmos::handler::CosmosChainHandler;

impl<Chain, Counterparty> ConsensusStateContext<CosmosChainHandler<Counterparty>>
    for CosmosChainHandler<Chain>
where
    Chain: Async,
    Counterparty: Async,
{
    type ConsensusState = ConsensusState;
}

#[async_trait]
impl<Chain, Counterparty> ConsensusStateQuerier<CosmosChainHandler<Counterparty>>
    for CosmosChainHandler<Chain>
where
    Chain: ChainHandle,
    Counterparty: Async,
{
    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<ConsensusState, Error> {
        let (any_consensus_state, _) = self
            .handle
            .query_consensus_state(
                QueryConsensusStateRequest {
                    client_id: client_id.clone(),
                    consensus_height: height.clone(),
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

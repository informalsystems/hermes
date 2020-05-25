use relayer_modules::ics24_host::identifier::ClientId;
use relayer_modules::Height;

use super::ibc_query;
use crate::chain::Chain;
use relayer_modules::ics02_client::query::{ClientFullStateResponse, QueryClientFullState};
use relayer_modules::ics02_client::query::{ConsensusStateResponse, QueryClientConsensusState};

use relayer_modules::error;

pub async fn query_client_full_state<C>(
    chain: &C,
    chain_height: Height,
    client_id: ClientId,
    prove: bool,
) -> Result<ClientFullStateResponse<C::ClientState>, error::Error>
where
    C: Chain,
{
    let query = QueryClientFullState::new(chain_height, client_id, prove);
    ibc_query(chain, query).await
}

pub async fn query_client_consensus_state<C>(
    chain: &C,
    chain_height: Height,
    client_id: ClientId,
    consensus_height: Height,
    prove: bool,
) -> Result<ConsensusStateResponse<C::ConsensusState>, error::Error>
where
    C: Chain,
{
    let query = QueryClientConsensusState::new(chain_height, client_id, consensus_height, prove);
    ibc_query(chain, query).await
}

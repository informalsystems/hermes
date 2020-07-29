use relayer_modules::ics24_host::identifier::ClientId;
use relayer_modules::Height;

use crate::chain::Chain;
use relayer_modules::ics02_client::query::{ClientFullStateResponse, ConsensusStateResponse};

use relayer_modules::error;

pub async fn query_client_full_state<C>(
    _chain: &C,
    _chain_height: Height,
    _client_id: ClientId,
    _prove: bool,
) -> Result<ClientFullStateResponse<C::ClientState>, error::Error>
where
    C: Chain,
{
    todo!("Implement generic query for client")
    /*
    let _query = QueryClientFullState::new(chain_height, client_id, prove);
    ibc_query(
        chain,
        Request {
            path: None,
            data: vec![],
            height: Some(TendermintHeight::from(chain_height)),
            prove,
        },
        query,
    )
    .await
    */
}

pub async fn query_client_consensus_state<C>(
    _chain: &C,
    _chain_height: Height,
    _client_id: ClientId,
    _consensus_height: Height,
    _prove: bool,
) -> Result<ConsensusStateResponse<C::ConsensusState>, error::Error>
where
    C: Chain,
{
    todo!("Implement generic query for client")
    /*
    let _query = QueryClientConsensusState::new(chain_height, client_id, consensus_height, prove);
    ibc_query(
        chain,
        Request {
            path: None,
            data: vec![],
            height: Some(TendermintHeight::from(chain_height)),
            prove,
        },
        query,
    )
    .await
    */
}

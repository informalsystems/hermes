use crate::types::error::Error;
use async_trait::async_trait;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use ibc::Height;

#[async_trait]
pub trait Endpoint {
    fn query_host_consensus_state(&self, height: &Height) -> Result<TmConsensusState, Error>;
}

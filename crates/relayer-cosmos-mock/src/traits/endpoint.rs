use crate::types::error::Error;
use async_trait::async_trait;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use ibc::core::timestamp::Timestamp;
use ibc::Height;
use tendermint_testgen::light_block::TmLightBlock;

#[async_trait]
pub trait Endpoint {
    fn query_current_height(&self) -> Result<Height, Error>;

    fn query_current_timestamp(&self) -> Result<Timestamp, Error>;

    fn query_light_block(&self, height: &Height) -> Result<TmLightBlock, Error>;

    fn query_host_consensus_state(&self, height: &Height) -> Result<TmConsensusState, Error>;
}

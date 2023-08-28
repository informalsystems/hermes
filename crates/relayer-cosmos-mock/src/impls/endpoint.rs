use crate::contexts::chain::MockCosmosContext;
use crate::traits::endpoint::Endpoint;
use crate::traits::handle::BasecoinHandle;
use crate::types::error::Error;

use async_trait::async_trait;
use basecoin_app::modules::ibc::AnyConsensusState;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use ibc::core::timestamp::Timestamp;
use ibc::core::ValidationContext;
use ibc::Height;
use tendermint_testgen::light_block::TmLightBlock;

#[async_trait]
impl<Handle: BasecoinHandle> Endpoint for MockCosmosContext<Handle> {
    fn query_current_height(&self) -> Result<Height, Error> {
        self.ibc_context().host_height().map_err(Error::from)
    }

    fn query_current_timestamp(&self) -> Result<Timestamp, Error> {
        self.ibc_context().host_timestamp().map_err(Error::from)
    }

    fn query_light_block(&self, height: &Height) -> Result<TmLightBlock, Error> {
        let blocks = self.handle.blocks();

        let revision_height = height.revision_height() as usize;

        if revision_height > blocks.len() {
            return Err(Error::invalid("block index out of bounds"));
        }

        Ok(blocks[revision_height - 1].clone())
    }

    fn query_host_consensus_state(&self, height: &Height) -> Result<TmConsensusState, Error> {
        let consensus_state = self.ibc_context().host_consensus_state(height)?;

        match consensus_state {
            AnyConsensusState::Tendermint(cs) => Ok(cs),
        }
    }
}

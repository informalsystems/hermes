use crate::contexts::chain::MockCosmosChain;
use crate::traits::endpoint::Endpoint;
use crate::types::error::Error;

use async_trait::async_trait;
use basecoin_app::modules::ibc::AnyConsensusState;
use ibc::clients::ics07_tendermint::consensus_state::ConsensusState as TmConsensusState;
use ibc::core::ValidationContext;
use ibc::Height;

#[async_trait]
impl Endpoint for MockCosmosChain {
    fn query_host_consensus_state(&self, height: &Height) -> Result<TmConsensusState, Error> {
        let consensus_state = self.ibc_context().host_consensus_state(height)?;

        match consensus_state {
            AnyConsensusState::Tendermint(cs) => Ok(cs),
        }
    }

    // fn query_consensus_state(&self, client_id: &ClientId) -> Result<TmConsensusState, Error> {
    // let current_height = self.get_current_height();

    // let cons_state_path = ClientConsensusStatePath::new(client_id, &current_height);

    // let (value, _) = self.query(cons_state_path, &current_height).await?;
    // let consensus_state =
    //     Protobuf::<RawConsensusState>::decode_vec(&value).map_err(BaseError::source)?;
    // }
}

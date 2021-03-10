use crate::chain::mock::MockChain;
use crate::chain::Chain;
use crate::error::Error;
use ibc::ics02_client::client_misbehaviour::AnyMisbehaviour;
use ibc::ics02_client::events::UpdateClient;
use ibc::ics24_host::identifier::ChainId;
use ibc::mock::host::HostBlock;
use ibc::Height;

/// A light client serving a mock chain.
pub struct LightClient {
    chain_id: ChainId,
}

impl LightClient {
    pub fn new(chain: &MockChain) -> LightClient {
        LightClient {
            chain_id: chain.id().clone(),
        }
    }

    /// Returns a LightBlock at the requested height `h`.
    fn light_block(&self, h: Height) -> <MockChain as Chain>::LightBlock {
        HostBlock::generate_tm_block(self.chain_id.clone(), h.revision_height)
    }
}

#[allow(unused_variables)]
impl super::LightClient<MockChain> for LightClient {
    fn latest_trusted(&self) -> Result<Option<<MockChain as Chain>::LightBlock>, Error> {
        unimplemented!()
    }

    fn verify_to_latest(&self) -> Result<<MockChain as Chain>::LightBlock, Error> {
        unimplemented!()
    }

    fn verify_to_target(&self, height: Height) -> Result<<MockChain as Chain>::LightBlock, Error> {
        Ok(self.light_block(height))
    }

    fn get_minimal_set(
        &self,
        latest_client_state_height: Height,
        target_height: Height,
    ) -> Result<Vec<Height>, Error> {
        unimplemented!()
    }

    fn build_misbehaviour(
        &self,
        update: UpdateClient,
        trusted_height: Height,
        latest_chain_height: Height,
    ) -> Result<Option<AnyMisbehaviour>, Error> {
        unimplemented!()
    }
}

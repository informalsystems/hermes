use tendermint_testgen::light_block::TmLightBlock;

use ibc::ics02_client::misbehaviour::AnyMisbehaviour;
use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::events::UpdateClient;
use ibc::ics24_host::identifier::ChainId;
use ibc::mock::host::HostBlock;
use ibc::Height;

use crate::chain::mock::MockChain;
use crate::chain::Chain;
use crate::error::Error;

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
    fn light_block(&self, h: Height) -> TmLightBlock {
        HostBlock::generate_tm_block(self.chain_id.clone(), h.revision_height)
    }
}

impl super::LightClient<MockChain> for LightClient {
    fn verify(
        &mut self,
        _trusted: Height,
        target: Height,
        _client_state: &AnyClientState,
    ) -> Result<TmLightBlock, Error> {
        Ok(self.light_block(target))
    }

    fn fetch(&mut self, height: Height) -> Result<TmLightBlock, Error> {
        Ok(self.light_block(height))
    }

    fn build_misbehaviour(
        &mut self,
        _client_state: &AnyClientState,
        _update: UpdateClient,
    ) -> Result<Option<AnyMisbehaviour>, Error> {
        unimplemented!()
    }
}

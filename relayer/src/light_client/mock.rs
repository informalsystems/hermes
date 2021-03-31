use crate::chain::mock::MockChain;
use crate::chain::Chain;
use crate::error::Error;
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

impl super::LightClient<MockChain> for LightClient {
    fn verify_to_latest(
        &mut self,
        _trusted: Height,
    ) -> Result<<MockChain as Chain>::LightBlock, Error> {
        unimplemented!()
    }

    fn verify_to_target(
        &mut self,
        _trusted: Height,
        target: Height,
    ) -> Result<<MockChain as Chain>::LightBlock, Error> {
        Ok(self.light_block(target))
    }

    fn fetch(&mut self, _height: Height) -> Result<<MockChain as Chain>::LightBlock, Error> {
        unimplemented!()
    }
}

use crate::chain::mock::MockChain;
use crate::chain::Chain;
use crate::error::Error;
use ibc::Height;

/// A light client serving a mock chain.
pub struct LightClient {}

#[allow(unused_variables)]
impl super::LightClient<MockChain> for LightClient {
    fn latest_trusted(&self) -> Result<Option<<MockChain as Chain>::LightBlock>, Error> {
        unimplemented!()
    }

    fn verify_to_latest(&self) -> Result<<MockChain as Chain>::LightBlock, Error> {
        unimplemented!()
    }

    fn verify_to_target(&self, height: Height) -> Result<<MockChain as Chain>::LightBlock, Error> {
        unimplemented!()
    }

    fn get_minimal_set(
        &self,
        latest_client_state_height: Height,
        target_height: Height,
    ) -> Result<Vec<Height>, Error> {
        unimplemented!()
    }
}

impl LightClient {
    pub fn new() -> LightClient {
        LightClient {}
    }
}

impl Default for LightClient {
    fn default() -> Self {
        Self::new()
    }
}

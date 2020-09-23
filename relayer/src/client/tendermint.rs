use std::sync::Arc;

use ibc::Height;

use tendermint_light_client::supervisor::Handle;
use tendermint_light_client::types::LightBlock;

pub struct LightClient {
    handle: Arc<Box<dyn Handle + Send + Sync>>,
}

impl super::LightClient<LightBlock> for LightClient {
    fn verify_latest(
        &mut self,
        now: std::time::SystemTime,
    ) -> Result<Option<LightBlock>, crate::error::Error> {
        todo!()
    }

    fn get_minimal_set(
        &mut self,
        latest_client_state_height: Height,
        target_height: Height,
    ) -> Result<Vec<LightBlock>, crate::error::Error> {
        todo!()
    }
}

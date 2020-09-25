use async_trait::async_trait;
use std::sync::Arc;
use tokio::task::spawn_blocking;

use ibc::Height;
use tendermint_light_client::supervisor::{Handle, SupervisorHandle};
use tendermint_light_client::types::LightBlock;

use crate::error;

pub struct LightClient {
    handle: SupervisorHandle,
}

impl LightClient {
    pub fn new(handle: SupervisorHandle) -> Self {
        Self { handle }
    }
}

#[async_trait]
impl super::LightClient<LightBlock> for LightClient {
    async fn verify_to_latest(&self) -> Result<LightBlock, error::Error> {
        let handle = self.handle.clone();

        spawn_blocking(move || {
            handle
                .verify_to_highest()
                .map_err(|e| error::Kind::LightClient.context(e).into())
        })
        .await
        .expect("task failed to execute to completion")
    }

    async fn verify_to_target(&self, height: Height) -> Result<LightBlock, error::Error> {
        let handle = self.handle.clone();

        spawn_blocking(move || {
            handle
                .verify_to_target(height)
                .map_err(|e| error::Kind::LightClient.context(e).into())
        })
        .await
        .expect("task failed to execute to completion")
    }

    async fn get_minimal_set(
        &self,
        latest_client_state_height: Height,
        target_height: Height,
    ) -> Result<Vec<Height>, error::Error> {
        todo!()
    }
}

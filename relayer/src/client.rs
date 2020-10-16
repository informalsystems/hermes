use std::cmp::Ordering;
use std::time::{Duration, SystemTime};

use anomaly::fail;
use async_trait::async_trait;
use tracing::{debug, info, warn};

use tendermint_light_client::supervisor::Handle;
use tendermint_light_client::types::{LightBlock, TrustThreshold};

use crate::chain;
use crate::error;

pub mod trust_options;
use ::tendermint::block::Height;
pub use trust_options::TrustOptions;

pub mod tendermint;

/// Defines a client from the point of view of the relayer.
#[async_trait]
pub trait LightClient<LightBlock> {
    /// Get the latest trusted state of the light client
    async fn latest_trusted(&self) -> Result<Option<LightBlock>, error::Error>;

    /// Fetch and verify the latest header from the chain
    async fn verify_to_latest(&self) -> Result<LightBlock, error::Error>;

    /// Fetch and verify the header from the chain at the given height
    async fn verify_to_target(&self, height: Height) -> Result<LightBlock, error::Error>;

    /// Compute the minimal ordered set of heights needed to update the light
    /// client state from from `latest_client_state_height` to `target_height`.
    async fn get_minimal_set(
        &self,
        latest_client_state_height: Height,
        target_height: Height,
    ) -> Result<Vec<Height>, error::Error>;
}

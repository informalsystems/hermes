use std::cmp::Ordering;
use std::time::{Duration, SystemTime};

use anomaly::fail;
use tracing::{debug, info, warn};

use ibc::Height;

use tendermint_light_client::supervisor::Handle;
use tendermint_light_client::types::{LightBlock, TrustThreshold};

use crate::chain;
use crate::error;
use crate::store::{self, StoreHeight};

pub mod trust_options;
pub use trust_options::TrustOptions;

pub mod tendermint;

/// Defines a client from the point of view of the relayer.
pub trait LightClient<LightBlock> {
    /// Fetch and verify the latest header from the chain
    ///
    /// If the fetched header is higher than the previous trusted state,
    /// and it verifies then we succeed and return it wrapped in `Some(_)`.
    ///
    /// If it is higher but does not verify we fail with an error.
    ///
    /// If it is lower we succeed but return `None`.
    ///
    /// If there is no trusted state yet we fail with an error.
    fn verify_latest(&mut self, now: SystemTime) -> Result<Option<LightBlock>, error::Error>;

    fn get_minimal_set(
        &mut self,
        latest_client_state_height: Height,
        target_height: Height,
    ) -> Result<Vec<LightBlock>, error::Error>;
}

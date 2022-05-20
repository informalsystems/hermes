pub mod client;
pub mod cosmos;
pub mod counterparty;
pub mod endpoint;
pub mod handle;
pub mod requests;
pub mod runtime;
pub mod tracking;

#[cfg(test)]
pub mod mock;

use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, Deserialize, Serialize)]
/// Types of chains the relayer can relay to and from
pub enum ChainType {
    /// Chains based on the Cosmos SDK
    CosmosSdk,

    /// Mock chain used for testing
    #[cfg(test)]
    Mock,
}

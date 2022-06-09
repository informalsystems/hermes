//! Data structures related to the denomination of coins used by the relayer.

use serde::{Deserialize, Serialize};

/// The denom trace
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DenomTrace {
    /// The chain of port/channel identifiers used for tracing the source of the coin.
    pub path: String,
    /// The base denomination for that coin
    pub base_denom: String,
}

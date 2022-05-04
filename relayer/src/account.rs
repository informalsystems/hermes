//! Data structures related to the accounts used by the relayer.

use serde::{Deserialize, Serialize};

/// The balance for a specific denom
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Balance {
    /// The amount of coins in the account, as a string to allow for large amounts
    pub amount: String,
    /// The denomination for that coin
    pub denom: String,
}

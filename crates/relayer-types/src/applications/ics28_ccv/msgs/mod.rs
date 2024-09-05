pub mod ccv_double_voting;
pub mod ccv_misbehaviour;
pub mod error;

use derive_more::Display;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display, Serialize, Deserialize)]
pub struct ConsumerId(String);

impl ConsumerId {
    pub const fn new(id: String) -> Self {
        Self(id)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

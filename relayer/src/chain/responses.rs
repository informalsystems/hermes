use core::fmt::{Display, Formatter};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CrossChainQueryResponse {
    id: String,
    data: String,
    height: u64,
}

impl CrossChainQueryResponse {
    pub fn new(id: String, data: String, height: u64) -> Self {
        Self { id, data, height }
    }
}

impl Display for CrossChainQueryResponse {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "id: {}, data: {}, height: {}",
            self.id, self.data, self.height
        )
    }
}

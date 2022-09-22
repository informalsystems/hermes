use crate::prelude::*;
use core::fmt::{Display, Formatter};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Default, Clone, Debug, PartialEq, Eq)]
pub struct CrossChainQueryPacket {
    pub id: String,
    pub path: String,
    pub height: String,
    pub timeout_height: String,
    pub timeout_timestamp: String,
}

impl Display for CrossChainQueryPacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "id: {}, path: {}, height: {}, timeout_height: {}, timeout_timestamp: {}",
            self.id, self.path, self.height, self.timeout_height, self.timeout_timestamp
        )
    }
}

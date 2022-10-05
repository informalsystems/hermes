use crate::prelude::*;
use core::fmt::{Display, Formatter};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Default, Clone, Debug, PartialEq, Eq)]
pub struct CrossChainQueryPacket {
    pub chain_id: String,
    pub id: String,
    pub path: String,
    pub height: String,
}

impl Display for CrossChainQueryPacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "chain_id: {}, id: {}, path: {}, height: {}",
            self.chain_id, self.id, self.path, self.height
        )
    }
}

use crate::prelude::*;
use core::fmt::{Display, Formatter};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CrossChainQueryPacket {
    pub id: String,
    pub path: String,
}

impl Display for CrossChainQueryPacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "id: {}, path: {}", self.id, self.path)
    }
}

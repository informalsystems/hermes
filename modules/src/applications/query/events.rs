use crate::prelude::*;

#[derive(Debug, Serialize, Clone, PartialEq, Eq)]
pub struct CrossChainQueryPacket {
    pub id: String,
    pub path: String,
}

use std::prelude::v1::*;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub struct CrossChainQueryResponse {
    pub chain_id: String,
    pub query_id: String,
    pub query_type: String,
    pub data: String,
    pub height: String,
}

impl CrossChainQueryResponse {
    pub fn new(
        chain_id: String,
        query_id: String,
        query_type: String,
        data: String,
        height: String,
    ) -> Self {
        Self {
            chain_id,
            query_id,
            query_type,
            data,
            height,
        }
    }
}
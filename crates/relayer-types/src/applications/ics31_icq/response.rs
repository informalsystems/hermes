use crate::signer::Signer;

use std::prelude::v1::*;
use serde::{Deserialize, Serialize};
use ibc_proto::google::protobuf::Any;

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

    pub fn to_any(&self, _signer: Signer) -> Any {
        let mut encoded = Vec::new();

        // TODO: encode tx submit cross chain query
        // let msg_submit_cross_chain_query_result = MsgSubmitCrossChainQueryResult {
        //     id: self.id.to_string(),
        //     query_height: self.height.parse().unwrap(),
        //     result: self.result,
        //     data: self.data.as_bytes().to_vec(),
        //     sender: handle.get_signer().unwrap().to_string(),
        //     query_sender: self.sender.to_string(),
        //     proof_specs: vec![],
        // };
        prost::Message::encode(&{}, &mut encoded).unwrap();
        Any {
            type_url: "".to_string(),
            value: encoded,
        }
    }
}
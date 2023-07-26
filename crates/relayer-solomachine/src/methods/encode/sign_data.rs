#![allow(non_snake_case)]

use ibc_proto::google::protobuf::Any;
use ibc_relayer_cosmos::methods::encode::encode_to_any;
use prost::{EncodeError, Message};

use crate::types::sign_data::SolomachineSignData;

const TYPE_URL: &str = "/ibc.lightclients.solomachine.v3.SignBytes";

#[derive(Message)]
pub struct ProtoSignBytes {
    #[prost(uint64, tag = "1")]
    pub sequence: u64,
    #[prost(uint64, tag = "2")]
    pub timestamp: u64,
    #[prost(string, tag = "3")]
    pub diversifier: String,
    #[prost(bytes = "vec", tag = "4")]
    pub path: Vec<u8>,
    #[prost(bytes = "vec", tag = "5")]
    pub data: Vec<u8>,
}

pub fn encode_sign_data(sign_data: &SolomachineSignData) -> Result<Any, EncodeError> {
    let proto_sign_bytes = ProtoSignBytes {
        sequence: sign_data.sequence,
        timestamp: sign_data.timestamp,
        diversifier: sign_data.diversifier.clone(),
        path: sign_data.path.clone(),
        data: sign_data.data.clone(),
    };

    encode_to_any(TYPE_URL, &proto_sign_bytes)
}

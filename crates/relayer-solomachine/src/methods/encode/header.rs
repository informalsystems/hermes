#![allow(non_snake_case)]

use ibc_proto::google::protobuf::Any;
use ibc_relayer_cosmos::methods::encode::encode_to_any;
use prost::{EncodeError, Message};
use secp256k1::SecretKey;

use crate::methods::encode::header_data::sign_header_data;
use crate::methods::encode::public_key::encode_public_key;
use crate::types::header::{SolomachineHeader, SolomachineSignHeaderData};

const TYPE_URL: &str = "/ibc.lightclients.solomachine.v3.Header";

#[derive(Message)]
pub struct ProtoHeader {
    #[prost(uint64, tag = "1")]
    pub timestamp: u64,
    #[prost(bytes = "vec", tag = "2")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "3")]
    pub new_public_key: ::core::option::Option<Any>,
    #[prost(string, tag = "4")]
    pub new_diversifier: ::prost::alloc::string::String,
}

pub fn encode_header(header: &SolomachineHeader) -> Result<Any, EncodeError> {
    let new_public_key = encode_public_key(&header.header_data.new_public_key);

    let proto_header = ProtoHeader {
        timestamp: header.timestamp,
        signature: header.signature.serialize_compact().into(),
        new_public_key: Some(new_public_key),
        new_diversifier: header.header_data.new_diversifier.clone(),
    };

    encode_to_any(TYPE_URL, &proto_header)
}

pub fn sign_and_create_header(
    secret_key: &SecretKey,
    header_data: &SolomachineSignHeaderData,
) -> Result<SolomachineHeader, EncodeError> {
    let signature = sign_header_data(secret_key, header_data)?;

    let header = SolomachineHeader {
        timestamp: header_data.timestamp,
        signature,
        header_data: header_data.header_data.clone(),
    };

    Ok(header)
}

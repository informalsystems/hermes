#![allow(non_snake_case)]

use ibc_proto::google::protobuf::Any;
use ibc_relayer_cosmos::methods::encode::{encode_protobuf, encode_to_any};
use prost::{EncodeError, Message};
use secp256k1::ecdsa::Signature;
use secp256k1::SecretKey;

use crate::methods::encode::public_key::encode_public_key;
use crate::methods::encode::sign_data::sign_with_data;
use crate::types::header::{SolomachineHeaderData, SolomachineSignHeaderData};
use crate::types::sign_data::SolomachineSignData;

const TYPE_URL: &str = "/ibc.lightclients.solomachine.v3.HeaderData";

#[derive(Message)]
pub struct ProtoHeaderData {
    #[prost(message, optional, tag = "1")]
    pub new_pub_key: ::core::option::Option<Any>,
    #[prost(string, tag = "2")]
    pub new_diversifier: String,
}

pub fn encode_header_data(header_data: &SolomachineHeaderData) -> Result<Any, EncodeError> {
    let encoded_public_key = encode_public_key(&header_data.new_public_key);

    let proto_header_data = ProtoHeaderData {
        new_pub_key: Some(encoded_public_key),
        new_diversifier: header_data.new_diversifier.clone(),
    };

    encode_to_any(TYPE_URL, &proto_header_data)
}

pub fn sign_header_data(
    secret_key: &SecretKey,
    header_data: &SolomachineSignHeaderData,
) -> Result<Signature, EncodeError> {
    let any_header_data = encode_header_data(&header_data.header_data)?;

    let header_bytes = encode_protobuf(&any_header_data)?;

    let sign_data = SolomachineSignData {
        sequence: header_data.sequence,
        timestamp: header_data.timestamp,
        diversifier: header_data.diversifier.clone(),
        path: "solomachine:header".into(),
        data: header_bytes,
    };

    sign_with_data(secret_key, &sign_data)
}

#![allow(non_snake_case)]

use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::data::{Single, Sum};
use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::Data;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_cosmos::methods::encode::{encode_any_to_bytes, encode_protobuf, encode_to_any};
use prost::{EncodeError, Message};
use secp256k1::ecdsa::Signature;
use secp256k1::SecretKey;

use crate::methods::encode::sign::sign_sha256;
use crate::types::sign_data::{SolomachineSignData, SolomachineTimestampedSignData};

use super::public_key::PublicKey;

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

pub fn to_proto_sign_bytes(sign_data: &SolomachineSignData) -> ProtoSignBytes {
    ProtoSignBytes {
        sequence: sign_data.sequence,
        timestamp: sign_data.timestamp,
        diversifier: sign_data.diversifier.clone(),
        path: sign_data.path.clone(),
        data: sign_data.data.clone(),
    }
}

pub fn sign_data_to_any(sign_data: &SolomachineSignData) -> Result<Any, EncodeError> {
    let proto_sign_bytes = to_proto_sign_bytes(sign_data);

    encode_to_any(TYPE_URL, &proto_sign_bytes)
}

pub fn sign_data_to_bytes(sign_data: &SolomachineSignData) -> Result<Vec<u8>, EncodeError> {
    let proto_sign_bytes = to_proto_sign_bytes(sign_data);

    encode_any_to_bytes(TYPE_URL, &proto_sign_bytes)
}

pub fn sign_with_data(
    secret_key: &SecretKey,
    sign_data: &SolomachineSignData,
) -> Result<Signature, EncodeError> {
    let proto_sign_bytes = to_proto_sign_bytes(sign_data);
    let sign_bytes = encode_protobuf(&proto_sign_bytes)?;

    let signature = sign_sha256(secret_key, &sign_bytes);

    Ok(signature)
}

pub fn timestamped_sign_with_data(
    sign_data: &SolomachineSignData,
    _public_key: PublicKey,
) -> Result<SolomachineTimestampedSignData, EncodeError> {
    let signature = sign_data_to_bytes(sign_data)?;

    let data = Data {
        sum: Some(Sum::Single(Single {
            /// SIGN_MODE_DIRECT specifies a signing mode which uses SignDoc and is
            /// verified with raw bytes from Tx.
            mode: 0,
            signature,
        })),
    };

    let bytes_data = encode_protobuf(&data).unwrap();

    Ok(SolomachineTimestampedSignData {
        signature_data: bytes_data,
        timestamp: sign_data.timestamp,
    })
}

/// TimestampedSignatureData contains the signature data and the timestamp of the
/// signature.
#[derive(Message)]
pub struct ProtoTimestampedSignatureData {
    #[prost(bytes = "vec", tag = "1")]
    pub signature_data: ::prost::alloc::vec::Vec<u8>,
    #[prost(uint64, tag = "2")]
    pub timestamp: u64,
}

pub fn to_proto_timestamped_sign_bytes(
    sign_data: &SolomachineTimestampedSignData,
) -> ProtoTimestampedSignatureData {
    ProtoTimestampedSignatureData {
        signature_data: sign_data.signature_data.clone(),
        timestamp: sign_data.timestamp,
    }
}

pub fn timestamped_sign_data_to_bytes(
    sign_data: &SolomachineTimestampedSignData,
) -> Result<Vec<u8>, EncodeError> {
    let proto_sign_bytes = to_proto_timestamped_sign_bytes(sign_data);

    encode_protobuf(&proto_sign_bytes)
}

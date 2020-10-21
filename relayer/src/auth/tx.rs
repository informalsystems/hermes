// use ibc_proto::tx::v1beta1::{Tx, TxBody, AuthInfo, SignDoc};
// use ibc::tx_msg::Msg;
//use crate::error::Error;
// use ibc_proto::tx::v1beta1::mode_info::{Single, Sum};
// use ibc_proto::tx::v1beta1::{AuthInfo, ModeInfo, SignDoc, SignerInfo, Tx, TxBody};
// use ibc::tx_msg::Msg;
// use ibc_proto::base::crypto::v1beta1::public_key::Sum as PK_Sum;
// use ibc_proto::base::crypto::v1beta1::PublicKey;
// use tendermint::{account::Id, chain::Id as ChainId, net::Address};
// use hex;
// use std::str::FromStr;
// Signer
// use k256::{
//     ecdsa::{signature::Signer, signature::Verifier, Signature, SigningKey, VerifyKey},
//     EncodedPoint, SecretKey,
// };

// pub struct TxWrapper {
//     tx: Tx,
//     body: Vec<u8>,
//     auth_info: Vec<u8>,
// }

// pub struct TxBuilder {
//
// }

//impl TxBuilder {
// pub fn build_tx<T: std::error::Error, U: Msg<ValidationError = T>>(msg: Vec<Box<U>>, memo: String) -> Result<TxBody, Error> {

// Create TxBody
// let body = TxBody {
//     messages: proto_msgs,
//     memo: "".to_string(),
//     timeout_height: 0,
//     extension_options: Vec::<prost_types::Any>::new(),
//     non_critical_extension_options: Vec::<prost_types::Any>::new(),
// };
//
// // A protobuf serialization of a TxBody
// let mut body_buf = Vec::new();
// prost::Message::encode(&body, &mut body_buf).unwrap();

// TODO: move this logic to tx builder
// let sum = Some(PK_Sum::Secp256k1(pubkey_bytes));
//
// let pk = Some(PublicKey { sum });
//
// let single = Single { mode: 1 };
// let sum_single = Some(Sum::Single(single));
// let mode = Some(ModeInfo { sum: sum_single });
//
// let signer_info = SignerInfo {
//     public_key: pk,
//     mode_info: mode,
//     sequence: 0,
// };
//
// let auth_info = AuthInfo {
//     signer_infos: vec![signer_info],
//     fee: None,
// };
//
// // A protobuf serialization of a AuthInfo
// let mut auth_buf = Vec::new();
// prost::Message::encode(&auth_info, &mut auth_buf).unwrap();
//
// let sign_doc = SignDoc {
//     body_bytes: body_buf.clone(),
//     auth_info_bytes: auth_buf.clone(),
//     chain_id: chain_config.clone().id.to_string(),
//     account_number: account_number,
// };
//
// // A protobuf serialization of a AuthInfo
// let mut signdoc_buf = Vec::new();
// prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();
//
// let signature: Signature = signing_key.sign(&signdoc_buf);
//
// status_info!("Signed Tx", "{:?}", signed_doc);
//
// let tx_raw = TxRaw {
//     body_bytes,
//     auth_info_bytes: auth_bytes,
//     signatures: vec![signature.as_ref().to_vec()],
// };
//
// let mut txraw_buf = Vec::new();
// prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();
// println!("{:?}", txraw_buf);
// }

// pub fn get_sign_doc(body: TxBody, auth: AuthInfo) -> Result<SignDoc, Error> {
//     // A protobuf serialization of a TxBody
//     let mut body_buf = Vec::new();
//     prost::Message::encode(&body, &mut body_buf).unwrap();
//
//     // A protobuf serialization of a AuthInfo
//     let mut auth_buf = Vec::new();
//     prost::Message::encode(&auth_info, &mut auth_buf).unwrap();
//
//     let sign_doc = SignDoc {
//         body_bytes: body_buf.clone(),
//         auth_info_bytes: auth_buf.clone(),
//         chain_id: chain_config.clone().id.to_string(),
//         account_number: account_number,
//     };
//
//     Ok(signdoc)
// }

// convenience function to get address from private key

//     fn get_account(pk: Vec<u8>) -> Vec<u8> {
//         use crypto::digest::Digest;
//         use crypto::ripemd160::Ripemd160;
//         use crypto::sha2::Sha256;
//         let mut seed = Sha256::new();
//         seed.input(pk.as_slice());
//         let mut bytes = vec![0; seed.output_bytes()];
//         seed.result(&mut bytes);
//
//         let mut hash = Ripemd160::new();
//         hash.input(bytes.as_slice());
//         let mut acct = vec![0; hash.output_bytes()];
//         hash.result(&mut acct);
//         acct.to_vec()
//     }
//}

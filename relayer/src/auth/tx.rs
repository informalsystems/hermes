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
//
//     let mut proto_msgs: Vec<prost_types::Any> = Vec::new();
//     let mut buf = Vec::new();
//
//     // Have a loop if new_builder takes more messages
//     // for now just encode one message
//     prost::Message::encode(&msg, &mut buf).unwrap();
//
//     // Create a proto any message
//     let any_msg = prost_types::Any {
//         type_url: "/ibc.connection.MsgConnectionOpenInit".to_string(),
//         value: buf,
//     };
//
//     // Add proto message
//     proto_msgs.push(any_msg);
//
//     // Create TxBody
//     let body = TxBody {
//         messages: proto_msgs,
//         memo,
//         timeout_height: 0,
//         extension_options: Vec::<prost_types::Any>::new(),
//         non_critical_extension_options: Vec::<prost_types::Any>::new(),
//     };
//
//     Ok(body)
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

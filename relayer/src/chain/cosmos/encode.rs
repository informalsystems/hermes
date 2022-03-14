use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{Fee, ModeInfo, SignDoc, SignerInfo, TxRaw};
use prost_types::Any;

use crate::chain::cosmos::types::SignedTx;
use crate::chain::cosmos::{auth_info_and_bytes, tx_body_and_bytes};
use crate::config::types::Memo;
use crate::config::AddressType;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::{sign_message, KeyEntry};

pub fn encode_key_bytes(key: &KeyEntry) -> Result<Vec<u8>, Error> {
    let mut pk_buf = Vec::new();

    prost::Message::encode(&key.public_key.public_key.to_bytes(), &mut pk_buf)
        .map_err(|e| Error::protobuf_encode("PublicKey".into(), e))?;

    Ok(pk_buf)
}

pub fn encode_sign_doc(
    chain_id: &ChainId,
    key: &KeyEntry,
    address_type: &AddressType,
    body_bytes: Vec<u8>,
    auth_info_bytes: Vec<u8>,
    account_number: u64,
) -> Result<Vec<u8>, Error> {
    let sign_doc = SignDoc {
        body_bytes,
        auth_info_bytes,
        chain_id: chain_id.to_string(),
        account_number,
    };

    // A protobuf serialization of a SignDoc
    let mut signdoc_buf = Vec::new();
    prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

    let signed = sign_message(key, signdoc_buf, address_type).map_err(Error::key_base)?;

    Ok(signed)
}

pub fn encode_signer_info(
    key_bytes: Vec<u8>,
    address_type: &AddressType,
    sequence: u64,
) -> Result<SignerInfo, Error> {
    let pk_type = match address_type {
        AddressType::Cosmos => "/cosmos.crypto.secp256k1.PubKey".to_string(),
        AddressType::Ethermint { pk_type } => pk_type.clone(),
    };
    // Create a MsgSend proto Any message
    let pk_any = Any {
        type_url: pk_type,
        value: key_bytes,
    };

    let single = Single { mode: 1 };
    let sum_single = Some(Sum::Single(single));
    let mode = Some(ModeInfo { sum: sum_single });
    let signer_info = SignerInfo {
        public_key: Some(pk_any),
        mode_info: mode,
        sequence,
    };
    Ok(signer_info)
}

pub fn encode_tx_raw(tx_raw: TxRaw) -> Result<Vec<u8>, Error> {
    let mut tx_bytes = Vec::new();
    prost::Message::encode(&tx_raw, &mut tx_bytes)
        .map_err(|e| Error::protobuf_encode("Transaction".to_string(), e))?;

    Ok(tx_bytes)
}

pub fn encode_tx_to_raw(
    config: &ChainConfig,
    messages: Vec<Any>,
    account_sequence: u64,
    key_entry: &KeyEntry,
    fee: &Fee,
    tx_memo: &Memo,
    account_number: u64,
) -> Result<SignedTx, Error> {
    let key_bytes = encode_key_bytes(key_entry)?;

    let signer = encode_signer_info(key_bytes, &config.address_type, account_sequence)?;

    let (body, body_bytes) = tx_body_and_bytes(messages, tx_memo)?;

    let (auth_info, auth_info_bytes) = auth_info_and_bytes(signer, fee.clone())?;

    let signed_doc = encode_sign_doc(
        &config.id,
        key_entry,
        &config.address_type,
        body_bytes.clone(),
        auth_info_bytes.clone(),
        account_number,
    )?;

    Ok(SignedTx {
        body,
        body_bytes,
        auth_info,
        auth_info_bytes,
        signatures: vec![signed_doc],
    })
}

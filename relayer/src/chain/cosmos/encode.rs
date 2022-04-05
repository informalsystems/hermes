use bech32::{ToBase32, Variant};
use core::str::FromStr;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};
use ibc_proto::google::protobuf::Any;
use tendermint::account::Id as AccountId;

use crate::chain::cosmos::types::account::{Account, AccountNumber, AccountSequence};
use crate::chain::cosmos::types::tx::SignedTx;
use crate::config::types::Memo;
use crate::config::AddressType;
use crate::config::ChainConfig;
use crate::error::Error;
use crate::keyring::{sign_message, KeyEntry};

pub fn sign_and_encode_tx(
    config: &ChainConfig,
    key_entry: &KeyEntry,
    account: &Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
    fee: &Fee,
) -> Result<Vec<u8>, Error> {
    let signed_tx = sign_tx(config, key_entry, account, tx_memo, messages, fee)?;

    let tx_raw = TxRaw {
        body_bytes: signed_tx.body_bytes,
        auth_info_bytes: signed_tx.auth_info_bytes,
        signatures: signed_tx.signatures,
    };

    encode_tx_raw(tx_raw)
}

pub fn sign_tx(
    config: &ChainConfig,
    key_entry: &KeyEntry,
    account: &Account,
    tx_memo: &Memo,
    messages: Vec<Any>,
    fee: &Fee,
) -> Result<SignedTx, Error> {
    let key_bytes = encode_key_bytes(key_entry)?;

    let signer = encode_signer_info(&config.address_type, account.sequence, key_bytes)?;

    let (body, body_bytes) = tx_body_and_bytes(messages, tx_memo)?;

    let (auth_info, auth_info_bytes) = auth_info_and_bytes(signer, fee.clone())?;

    let signed_doc = encode_sign_doc(
        &config.id,
        key_entry,
        &config.address_type,
        account.number,
        auth_info_bytes.clone(),
        body_bytes.clone(),
    )?;

    Ok(SignedTx {
        body,
        body_bytes,
        auth_info,
        auth_info_bytes,
        signatures: vec![signed_doc],
    })
}

fn encode_key_bytes(key: &KeyEntry) -> Result<Vec<u8>, Error> {
    let mut pk_buf = Vec::new();

    prost::Message::encode(&key.public_key.public_key.to_bytes(), &mut pk_buf)
        .map_err(|e| Error::protobuf_encode("PublicKey".into(), e))?;

    Ok(pk_buf)
}

fn encode_sign_doc(
    chain_id: &ChainId,
    key: &KeyEntry,
    address_type: &AddressType,
    account_number: AccountNumber,
    auth_info_bytes: Vec<u8>,
    body_bytes: Vec<u8>,
) -> Result<Vec<u8>, Error> {
    let sign_doc = SignDoc {
        body_bytes,
        auth_info_bytes,
        chain_id: chain_id.to_string(),
        account_number: account_number.to_u64(),
    };

    // A protobuf serialization of a SignDoc
    let mut signdoc_buf = Vec::new();
    prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

    let signed = sign_message(key, signdoc_buf, address_type).map_err(Error::key_base)?;

    Ok(signed)
}

fn encode_signer_info(
    address_type: &AddressType,
    sequence: AccountSequence,
    key_bytes: Vec<u8>,
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
        sequence: sequence.to_u64(),
    };
    Ok(signer_info)
}

fn encode_tx_raw(tx_raw: TxRaw) -> Result<Vec<u8>, Error> {
    let mut tx_bytes = Vec::new();
    prost::Message::encode(&tx_raw, &mut tx_bytes)
        .map_err(|e| Error::protobuf_encode("Transaction".to_string(), e))?;

    Ok(tx_bytes)
}

pub fn encode_to_bech32(address: &str, account_prefix: &str) -> Result<String, Error> {
    let account = AccountId::from_str(address)
        .map_err(|e| Error::invalid_key_address(address.to_string(), e))?;

    let encoded = bech32::encode(account_prefix, account.to_base32(), Variant::Bech32)
        .map_err(Error::bech32_encoding)?;

    Ok(encoded)
}

fn auth_info_and_bytes(signer_info: SignerInfo, fee: Fee) -> Result<(AuthInfo, Vec<u8>), Error> {
    let auth_info = AuthInfo {
        signer_infos: vec![signer_info],
        fee: Some(fee),
    };

    // A protobuf serialization of a AuthInfo
    let mut auth_buf = Vec::new();

    prost::Message::encode(&auth_info, &mut auth_buf)
        .map_err(|e| Error::protobuf_encode(String::from("AuthInfo"), e))?;

    Ok((auth_info, auth_buf))
}

fn tx_body_and_bytes(proto_msgs: Vec<Any>, memo: &Memo) -> Result<(TxBody, Vec<u8>), Error> {
    // Create TxBody
    let body = TxBody {
        messages: proto_msgs.to_vec(),
        memo: memo.to_string(),
        timeout_height: 0_u64,
        extension_options: Vec::<Any>::new(),
        non_critical_extension_options: Vec::<Any>::new(),
    };

    // A protobuf serialization of a TxBody
    let mut body_buf = Vec::new();

    prost::Message::encode(&body, &mut body_buf)
        .map_err(|e| Error::protobuf_encode(String::from("TxBody"), e))?;

    Ok((body, body_buf))
}

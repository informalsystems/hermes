use core::str::FromStr;

use bech32::{
    ToBase32,
    Variant,
};
use ibc_proto::{
    cosmos::tx::v1beta1::{
        mode_info::{
            Single,
            Sum,
        },
        AuthInfo,
        Fee,
        ModeInfo,
        SignDoc,
        SignerInfo,
        TxBody,
        TxRaw,
    },
    google::protobuf::Any,
};
use ibc_relayer_types::{
    core::{
        ics02_client::error::Error as ClientError,
        ics24_host::identifier::ChainId,
    },
    signer::Signer,
};
use prost::Message;
use tendermint::account::Id as AccountId;

use crate::{
    chain::cosmos::types::{
        account::{
            Account,
            AccountNumber,
            AccountSequence,
        },
        config::TxConfig,
        tx::SignedTx,
    },
    config::{
        types::Memo,
        AddressType,
    },
    error::Error,
    keyring::{
        Secp256k1KeyPair,
        SigningKeyPair,
    },
};

pub fn sign_and_encode_tx(
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
    fee: &Fee,
) -> Result<Vec<u8>, Error> {
    let signed_tx = sign_tx(config, key_pair, account, tx_memo, messages, fee)?;

    let tx_raw = TxRaw {
        body_bytes: signed_tx.body_bytes,
        auth_info_bytes: signed_tx.auth_info_bytes,
        signatures: signed_tx.signatures,
    };

    encode_tx_raw(tx_raw)
}

/// Length information for an encoded transaction.
pub struct EncodedTxMetrics {
    /// Length of the encoded message, excluding the `body_bytes` field.
    pub envelope_len: usize,
    /// Length of the byte array in the `body_bytes` field of the `TxRaw` message.
    pub body_bytes_len: usize,
}

pub fn encoded_tx_metrics(
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
    fee: &Fee,
) -> Result<EncodedTxMetrics, Error> {
    let signed_tx = sign_tx(config, key_pair, account, tx_memo, messages, fee)?;

    let tx_raw = TxRaw {
        body_bytes: signed_tx.body_bytes,
        auth_info_bytes: signed_tx.auth_info_bytes,
        signatures: signed_tx.signatures,
    };

    let total_len = tx_raw.encoded_len();
    let body_bytes_len = tx_raw.body_bytes.len();
    let envelope_len = if body_bytes_len == 0 {
        total_len
    } else {
        total_len - 1 - prost::length_delimiter_len(body_bytes_len) - body_bytes_len
    };

    Ok(EncodedTxMetrics {
        envelope_len,
        body_bytes_len,
    })
}

pub fn sign_tx(
    config: &TxConfig,
    key_pair: &Secp256k1KeyPair,
    account: &Account,
    tx_memo: &Memo,
    messages: &[Any],
    fee: &Fee,
) -> Result<SignedTx, Error> {
    let key_bytes = encode_key_bytes(key_pair)?;

    let signer = encode_signer_info(&config.address_type, account.sequence, key_bytes)?;

    let (body, body_bytes) =
        tx_body_and_bytes(messages, tx_memo, config.extension_options.clone())?;

    let (auth_info, auth_info_bytes) = auth_info_and_bytes(signer, fee.clone())?;

    let signed_doc = encode_sign_doc(
        &config.chain_id,
        key_pair,
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

fn encode_key_bytes(key_pair: &Secp256k1KeyPair) -> Result<Vec<u8>, Error> {
    let mut pk_buf = Vec::new();

    prost::Message::encode(&key_pair.public_key.serialize().to_vec(), &mut pk_buf)
        .map_err(|e| Error::protobuf_encode("PublicKey".into(), e))?;

    Ok(pk_buf)
}

fn encode_sign_doc(
    chain_id: &ChainId,
    key_pair: &Secp256k1KeyPair,
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

    let signed = key_pair.sign(&signdoc_buf).map_err(Error::key_base)?;

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
        AddressType::Astria => "/cosmos.crypto.ed25519.PubKey".to_string(), // TODO ?
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

        // Since Cosmos SDK v0.46.0
        tip: None,
    };

    // A protobuf serialization of a AuthInfo
    let mut auth_buf = Vec::new();

    prost::Message::encode(&auth_info, &mut auth_buf)
        .map_err(|e| Error::protobuf_encode(String::from("AuthInfo"), e))?;

    Ok((auth_info, auth_buf))
}

fn tx_body_and_bytes(
    proto_msgs: &[Any],
    memo: &Memo,
    extension_options: Vec<Any>,
) -> Result<(TxBody, Vec<u8>), Error> {
    // Create TxBody
    let body = TxBody {
        messages: proto_msgs.to_vec(),
        memo: memo.to_string(),
        timeout_height: 0_u64,
        extension_options,
        non_critical_extension_options: Vec::<Any>::new(),
    };

    // A protobuf serialization of a TxBody
    let mut body_buf = Vec::new();

    prost::Message::encode(&body, &mut body_buf)
        .map_err(|e| Error::protobuf_encode(String::from("TxBody"), e))?;

    Ok((body, body_buf))
}

pub fn key_pair_to_signer(key_pair: &Secp256k1KeyPair) -> Result<Signer, Error> {
    let signer = key_pair
        .account()
        .parse()
        .map_err(|e| Error::ics02(ClientError::signer(e)))?;

    Ok(signer)
}

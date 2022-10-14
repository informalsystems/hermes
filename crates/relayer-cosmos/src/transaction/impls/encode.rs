use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw};
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::types::account::{AccountNumber, AccountSequence};
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer::config::types::Memo;
use ibc_relayer::config::AddressType;
use ibc_relayer::keyring::{errors::Error as KeyringError, sign_message, KeyEntry};
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use prost::EncodeError;

use crate::transaction::traits::field::{FieldGetter, HasField};
use crate::transaction::types::ExtensionOptions;

pub trait CanSignAndEncodeTx: HasError {
    fn sign_and_encode_tx(&self, messages: &[Any], fee: &Fee) -> Result<Vec<u8>, Self::Error>;
}

impl<Context> CanSignAndEncodeTx for Context
where
    Context: InjectError<EncodeError> + CanSignTx,
{
    fn sign_and_encode_tx(&self, messages: &[Any], fee: &Fee) -> Result<Vec<u8>, Self::Error> {
        let signed_tx = self.sign_tx(messages, fee)?;

        let tx_raw = TxRaw {
            body_bytes: signed_tx.body_bytes,
            auth_info_bytes: signed_tx.auth_info_bytes,
            signatures: signed_tx.signatures,
        };

        let mut tx_bytes = Vec::new();

        prost::Message::encode(&tx_raw, &mut tx_bytes).map_err(Context::inject_error)?;

        Ok(tx_bytes)
    }
}

pub trait CanSignTx: HasError {
    fn sign_tx(&self, messages: &[Any], fee: &Fee) -> Result<SignedTx, Self::Error>;
}

impl<Context> CanSignTx for Context
where
    Context: HasError
        + CanEncodeKeyBytes
        + CanEncodeSignerInfo
        + CanEncodeTxBodyAndBytes
        + CanEncodeAuthInfoAndBytes
        + CanEncodeSignDoc,
{
    fn sign_tx(&self, messages: &[Any], fee: &Fee) -> Result<SignedTx, Self::Error> {
        let key_bytes = self.encode_key_bytes()?;

        let signer = self.encode_signer_info(key_bytes)?;

        let (body, body_bytes) = self.encode_tx_body_and_bytes(messages)?;

        let (auth_info, auth_info_bytes) = Self::encode_auth_info_and_bytes(signer, fee.clone())?;

        let signed_doc = self.encode_sign_doc(auth_info_bytes.clone(), body_bytes.clone())?;

        Ok(SignedTx {
            body,
            body_bytes,
            auth_info,
            auth_info_bytes,
            signatures: vec![signed_doc],
        })
    }
}

trait CanEncodeKeyBytes: HasError {
    fn encode_key_bytes(&self) -> Result<Vec<u8>, Self::Error>;
}

impl<Context> CanEncodeKeyBytes for Context
where
    Context: InjectError<EncodeError>,
    Context: HasField<KeyEntry>,
{
    fn encode_key_bytes(&self) -> Result<Vec<u8>, Self::Error> {
        let key_entry = KeyEntry::get_from(self);

        let public_key_bytes = key_entry.public_key.to_pub().to_bytes();

        let mut pk_buf = Vec::new();

        prost::Message::encode(&public_key_bytes, &mut pk_buf).map_err(Context::inject_error)?;

        Ok(pk_buf)
    }
}

trait CanEncodeSignerInfo: HasError {
    fn encode_signer_info(&self, key_bytes: Vec<u8>) -> Result<SignerInfo, Self::Error>;
}

impl<Context> CanEncodeSignerInfo for Context
where
    Context: HasError + HasField<AccountSequence> + HasField<AddressType>,
{
    fn encode_signer_info(&self, key_bytes: Vec<u8>) -> Result<SignerInfo, Self::Error> {
        let address_type = AddressType::get_from(self);
        let account_sequence = AccountSequence::get_from(self);

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
            sequence: account_sequence.to_u64(),
        };
        Ok(signer_info)
    }
}

trait CanEncodeTxBodyAndBytes: HasError {
    fn encode_tx_body_and_bytes(&self, messages: &[Any]) -> Result<(TxBody, Vec<u8>), Self::Error>;
}

impl<Context> CanEncodeTxBodyAndBytes for Context
where
    Context: InjectError<EncodeError> + HasField<Memo> + HasField<ExtensionOptions>,
{
    fn encode_tx_body_and_bytes(&self, messages: &[Any]) -> Result<(TxBody, Vec<u8>), Self::Error> {
        let memo = Memo::get_from(self);
        let extension_options = ExtensionOptions::get_from(self);

        let body = TxBody {
            messages: messages.to_vec(),
            memo: memo.to_string(),
            timeout_height: 0_u64,
            extension_options: extension_options.0.clone(),
            non_critical_extension_options: Vec::<Any>::new(),
        };

        // A protobuf serialization of a TxBody
        let mut body_buf = Vec::new();

        prost::Message::encode(&body, &mut body_buf).map_err(Context::inject_error)?;

        Ok((body, body_buf))
    }
}

trait CanEncodeAuthInfoAndBytes: HasError {
    fn encode_auth_info_and_bytes(
        signer_info: SignerInfo,
        fee: Fee,
    ) -> Result<(AuthInfo, Vec<u8>), Self::Error>;
}

impl<Context> CanEncodeAuthInfoAndBytes for Context
where
    Context: InjectError<EncodeError>,
{
    fn encode_auth_info_and_bytes(
        signer_info: SignerInfo,
        fee: Fee,
    ) -> Result<(AuthInfo, Vec<u8>), Self::Error> {
        let auth_info = AuthInfo {
            signer_infos: vec![signer_info],
            fee: Some(fee),

            // Since Cosmos SDK v0.46.0
            tip: None,
        };

        // A protobuf serialization of a AuthInfo
        let mut auth_buf = Vec::new();

        prost::Message::encode(&auth_info, &mut auth_buf).map_err(Context::inject_error)?;

        Ok((auth_info, auth_buf))
    }
}

trait CanEncodeSignDoc: HasError {
    fn encode_sign_doc(
        &self,
        auth_info_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
    ) -> Result<Vec<u8>, Self::Error>;
}

impl<Context> CanEncodeSignDoc for Context
where
    Context:
        HasField<ChainId> + HasField<AccountNumber> + InjectError<EncodeError> + CanSignMessage,
{
    fn encode_sign_doc(
        &self,
        auth_info_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
    ) -> Result<Vec<u8>, Self::Error> {
        let chain_id = ChainId::get_from(self);
        let account_number = AccountNumber::get_from(self);

        let sign_doc = SignDoc {
            body_bytes,
            auth_info_bytes,
            chain_id: chain_id.to_string(),
            account_number: account_number.to_u64(),
        };

        // A protobuf serialization of a SignDoc
        let mut signdoc_buf = Vec::new();
        prost::Message::encode(&sign_doc, &mut signdoc_buf).map_err(Context::inject_error)?;

        let signed = self.sign_message(signdoc_buf)?;

        Ok(signed)
    }
}

trait CanSignMessage: HasError {
    fn sign_message(&self, message: Vec<u8>) -> Result<Vec<u8>, Self::Error>;
}

impl<Context> CanSignMessage for Context
where
    Context: HasField<AddressType> + HasField<KeyEntry> + InjectError<KeyringError>,
{
    fn sign_message(&self, message: Vec<u8>) -> Result<Vec<u8>, Self::Error> {
        let address_type = AddressType::get_from(self);
        let key_entry = KeyEntry::get_from(self);

        sign_message(key_entry, message, address_type).map_err(Context::inject_error)
    }
}

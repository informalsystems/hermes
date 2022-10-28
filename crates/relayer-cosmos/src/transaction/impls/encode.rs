use async_trait::async_trait;
use ibc_proto::cosmos::tx::v1beta1::mode_info::{Single, Sum};
use ibc_proto::cosmos::tx::v1beta1::{AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody};
use ibc_proto::google::protobuf::Any;
use ibc_relayer::chain::cosmos::types::account::AccountSequence;
use ibc_relayer::chain::cosmos::types::tx::SignedTx;
use ibc_relayer::config::AddressType;
use ibc_relayer::keyring::errors::Error as KeyringError;
use ibc_relayer::keyring::sign_message;
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use prost::EncodeError;

use crate::transaction::traits::fields::{
    HasAccountNumber, HasAddressType, HasChainId, HasExtensionOptions, HasKeyEntry, HasMemo,
};

#[async_trait]
pub trait CanSignTx: HasError {
    async fn sign_tx(
        &self,
        fee: &Fee,
        sequence: &AccountSequence,
        messages: &[Any],
    ) -> Result<SignedTx, Self::Error>;
}

trait CanEncodeKeyBytes: HasError {
    fn encode_key_bytes(&self) -> Result<Vec<u8>, Self::Error>;
}

#[async_trait]
trait CanEncodeSignerInfo: HasError {
    async fn encode_signer_info(
        &self,
        account_sequence: &AccountSequence,
        key_bytes: Vec<u8>,
    ) -> Result<SignerInfo, Self::Error>;
}

trait CanEncodeTxBodyAndBytes: HasError {
    fn encode_tx_body_and_bytes(&self, messages: &[Any]) -> Result<(TxBody, Vec<u8>), Self::Error>;
}

trait CanEncodeAuthInfoAndBytes: HasError {
    fn encode_auth_info_and_bytes(
        signer_info: SignerInfo,
        fee: Fee,
    ) -> Result<(AuthInfo, Vec<u8>), Self::Error>;
}

trait CanSignMessage: HasError {
    fn sign_message(&self, message: Vec<u8>) -> Result<Vec<u8>, Self::Error>;
}

#[async_trait]
trait CanEncodeSignDoc: HasError {
    async fn encode_sign_doc(
        &self,
        auth_info_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
    ) -> Result<Vec<u8>, Self::Error>;
}

#[async_trait]
impl<Context> CanSignTx for Context
where
    Context: HasError
        + CanEncodeKeyBytes
        + CanEncodeSignerInfo
        + CanEncodeTxBodyAndBytes
        + CanEncodeAuthInfoAndBytes
        + CanEncodeSignDoc,
{
    async fn sign_tx(
        &self,
        fee: &Fee,
        sequence: &AccountSequence,
        messages: &[Any],
    ) -> Result<SignedTx, Self::Error> {
        let key_bytes = self.encode_key_bytes()?;

        let signer = self.encode_signer_info(sequence, key_bytes).await?;

        let (body, body_bytes) = self.encode_tx_body_and_bytes(messages)?;

        let (auth_info, auth_info_bytes) = Self::encode_auth_info_and_bytes(signer, fee.clone())?;

        let signed_doc = self
            .encode_sign_doc(auth_info_bytes.clone(), body_bytes.clone())
            .await?;

        Ok(SignedTx {
            body,
            body_bytes,
            auth_info,
            auth_info_bytes,
            signatures: vec![signed_doc],
        })
    }
}

impl<Context> CanEncodeKeyBytes for Context
where
    Context: InjectError<EncodeError>,
    Context: HasKeyEntry,
{
    fn encode_key_bytes(&self) -> Result<Vec<u8>, Self::Error> {
        let key_entry = self.key_entry();

        let public_key_bytes = key_entry.public_key.to_pub().to_bytes();

        let mut pk_buf = Vec::new();

        prost::Message::encode(&public_key_bytes, &mut pk_buf).map_err(Context::inject_error)?;

        Ok(pk_buf)
    }
}

#[async_trait]
impl<Context> CanEncodeSignerInfo for Context
where
    Context: HasError + HasAddressType,
{
    async fn encode_signer_info(
        &self,
        account_sequence: &AccountSequence,
        key_bytes: Vec<u8>,
    ) -> Result<SignerInfo, Self::Error> {
        let address_type = self.address_type();

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

impl<Context> CanEncodeTxBodyAndBytes for Context
where
    Context: InjectError<EncodeError> + HasMemo + HasExtensionOptions,
{
    fn encode_tx_body_and_bytes(&self, messages: &[Any]) -> Result<(TxBody, Vec<u8>), Self::Error> {
        let memo = self.memo();
        let extension_options = self.extension_options();

        let body = TxBody {
            messages: messages.to_vec(),
            memo: memo.to_string(),
            timeout_height: 0_u64,
            extension_options: extension_options.clone(),
            non_critical_extension_options: Vec::<Any>::new(),
        };

        // A protobuf serialization of a TxBody
        let mut body_buf = Vec::new();

        prost::Message::encode(&body, &mut body_buf).map_err(Context::inject_error)?;

        Ok((body, body_buf))
    }
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

#[async_trait]
impl<Context> CanEncodeSignDoc for Context
where
    Context: HasChainId + HasAccountNumber + InjectError<EncodeError> + CanSignMessage,
{
    async fn encode_sign_doc(
        &self,
        auth_info_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
    ) -> Result<Vec<u8>, Self::Error> {
        let chain_id = self.chain_id();
        let account_number = self.account_number();

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

impl<Context> CanSignMessage for Context
where
    Context: HasAddressType + HasKeyEntry + InjectError<KeyringError>,
{
    fn sign_message(&self, message: Vec<u8>) -> Result<Vec<u8>, Self::Error> {
        let address_type = self.address_type();
        let key_entry = self.key_entry();

        sign_message(key_entry, message, address_type).map_err(Context::inject_error)
    }
}

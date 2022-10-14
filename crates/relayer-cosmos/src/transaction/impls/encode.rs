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

pub struct SignTx;

pub trait CanSignAndEncodeTx<Context: HasError> {
    fn sign_and_encode_tx(
        context: &Context,
        messages: &[Any],
        fee: &Fee,
    ) -> Result<Vec<u8>, Context::Error>;
}

impl<Context> CanSignAndEncodeTx<Context> for SignTx
where
    Context: InjectError<EncodeError>,
    Self: CanSignTx<Context>,
{
    fn sign_and_encode_tx(
        context: &Context,
        messages: &[Any],
        fee: &Fee,
    ) -> Result<Vec<u8>, Context::Error> {
        let signed_tx = Self::sign_tx(context, messages, fee)?;

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

pub trait CanSignTx<Context: HasError> {
    fn sign_tx(context: &Context, messages: &[Any], fee: &Fee) -> Result<SignedTx, Context::Error>;
}

impl<Context> CanSignTx<Context> for SignTx
where
    Context: HasError,
    Self: CanEncodeKeyBytes<Context>
        + CanEncodeSignerInfo<Context>
        + CanEncodeTxBodyAndBytes<Context>
        + CanEncodeAuthInfoAndBytes<Context>
        + CanEncodeSignDoc<Context>,
{
    fn sign_tx(context: &Context, messages: &[Any], fee: &Fee) -> Result<SignedTx, Context::Error> {
        let key_bytes = Self::encode_key_bytes(context)?;

        let signer = Self::encode_signer_info(context, key_bytes)?;

        let (body, body_bytes) = Self::encode_tx_body_and_bytes(context, messages)?;

        let (auth_info, auth_info_bytes) = Self::encode_auth_info_and_bytes(signer, fee.clone())?;

        let signed_doc =
            Self::encode_sign_doc(context, auth_info_bytes.clone(), body_bytes.clone())?;

        Ok(SignedTx {
            body,
            body_bytes,
            auth_info,
            auth_info_bytes,
            signatures: vec![signed_doc],
        })
    }
}

trait CanEncodeKeyBytes<Context: HasError> {
    fn encode_key_bytes(context: &Context) -> Result<Vec<u8>, Context::Error>;
}

impl<Context> CanEncodeKeyBytes<Context> for SignTx
where
    Context: InjectError<EncodeError>,
    Context: HasField<KeyEntry>,
{
    fn encode_key_bytes(context: &Context) -> Result<Vec<u8>, Context::Error> {
        let key_entry = KeyEntry::get_from(context);

        let public_key_bytes = key_entry.public_key.to_pub().to_bytes();

        let mut pk_buf = Vec::new();

        prost::Message::encode(&public_key_bytes, &mut pk_buf).map_err(Context::inject_error)?;

        Ok(pk_buf)
    }
}

trait CanEncodeSignerInfo<Context: HasError> {
    fn encode_signer_info(
        context: &Context,
        key_bytes: Vec<u8>,
    ) -> Result<SignerInfo, Context::Error>;
}

impl<Context> CanEncodeSignerInfo<Context> for SignTx
where
    Context: HasError,
    Context: HasField<AccountSequence>,
    Context: HasField<AddressType>,
{
    fn encode_signer_info(
        context: &Context,
        key_bytes: Vec<u8>,
    ) -> Result<SignerInfo, Context::Error> {
        let address_type = AddressType::get_from(context);
        let account_sequence = AccountSequence::get_from(context);

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

trait CanEncodeTxBodyAndBytes<Context: HasError> {
    fn encode_tx_body_and_bytes(
        context: &Context,
        messages: &[Any],
    ) -> Result<(TxBody, Vec<u8>), Context::Error>;
}

impl<Context> CanEncodeTxBodyAndBytes<Context> for SignTx
where
    Context: InjectError<EncodeError>,
    Context: HasField<Memo>,
    Context: HasField<ExtensionOptions>,
{
    fn encode_tx_body_and_bytes(
        context: &Context,
        messages: &[Any],
    ) -> Result<(TxBody, Vec<u8>), Context::Error> {
        let memo = Memo::get_from(context);
        let extension_options = ExtensionOptions::get_from(context);

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

trait CanEncodeAuthInfoAndBytes<Context: HasError> {
    fn encode_auth_info_and_bytes(
        signer_info: SignerInfo,
        fee: Fee,
    ) -> Result<(AuthInfo, Vec<u8>), Context::Error>;
}

impl<Context> CanEncodeAuthInfoAndBytes<Context> for SignTx
where
    Context: InjectError<EncodeError>,
{
    fn encode_auth_info_and_bytes(
        signer_info: SignerInfo,
        fee: Fee,
    ) -> Result<(AuthInfo, Vec<u8>), Context::Error> {
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

trait CanEncodeSignDoc<Context: HasError> {
    fn encode_sign_doc(
        context: &Context,
        auth_info_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
    ) -> Result<Vec<u8>, Context::Error>;
}

impl<Context> CanEncodeSignDoc<Context> for SignTx
where
    Context: HasField<ChainId>,
    Context: HasField<AccountNumber>,
    Context: InjectError<EncodeError>,
    Self: CanSignMessage<Context>,
{
    fn encode_sign_doc(
        context: &Context,
        auth_info_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
    ) -> Result<Vec<u8>, Context::Error> {
        let chain_id = ChainId::get_from(context);
        let account_number = AccountNumber::get_from(context);

        let sign_doc = SignDoc {
            body_bytes,
            auth_info_bytes,
            chain_id: chain_id.to_string(),
            account_number: account_number.to_u64(),
        };

        // A protobuf serialization of a SignDoc
        let mut signdoc_buf = Vec::new();
        prost::Message::encode(&sign_doc, &mut signdoc_buf).map_err(Context::inject_error)?;

        let signed = Self::sign_message(context, signdoc_buf)?;

        Ok(signed)
    }
}

trait CanSignMessage<Context: HasError> {
    fn sign_message(context: &Context, message: Vec<u8>) -> Result<Vec<u8>, Context::Error>;
}

impl<Context> CanSignMessage<Context> for SignTx
where
    Context: HasField<AddressType>,
    Context: HasField<KeyEntry>,
    Context: InjectError<KeyringError>,
{
    fn sign_message(context: &Context, message: Vec<u8>) -> Result<Vec<u8>, Context::Error> {
        let address_type = AddressType::get_from(context);
        let key_entry = KeyEntry::get_from(context);

        sign_message(key_entry, message, address_type).map_err(Context::inject_error)
    }
}

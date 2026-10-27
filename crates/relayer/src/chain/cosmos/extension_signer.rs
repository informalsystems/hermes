//! Pluggable transaction co-signers.
//!
//! Some chains require a second signature next to the classical one, carried
//! as a `TxBody` extension option (for example a post-quantum signature). An
//! [`ExtensionSigner`] is called once per transaction, after the fee, gas
//! limit and sequence are final and before the classical `SIGN_MODE_DIRECT`
//! signature is made, so the classical signature, gas simulation and batch
//! sizing all see the final transaction.
//!
//! Chains without an extension signer are unaffected: their transactions are
//! byte for byte what they were before.

use core::fmt::Debug;

use ibc_proto::cosmos::tx::v1beta1::TxBody;
use ibc_proto::google::protobuf::Any;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::config::types::Memo;
use crate::error::Error;

/// What an [`ExtensionSigner`] signs over.
#[derive(Debug)]
pub struct ExtensionSignRequest<'a> {
    pub chain_id: &'a ChainId,
    /// The encoded `TxBody`, without the options this signer adds.
    pub body_bytes: &'a [u8],
    /// The encoded, final `AuthInfo`.
    pub auth_info_bytes: &'a [u8],
    pub account_number: u64,
    pub sequence: u64,
}

/// Adds extension options (typically an additional signature) to a
/// transaction body before it is signed.
pub trait ExtensionSigner: Send + Sync + Debug {
    /// Returns the options to append to the body's `extension_options`.
    fn extension_options(&self, request: &ExtensionSignRequest<'_>) -> Result<Vec<Any>, String>;
}

/// Asks `signer`, if any, for its extension options over `body_bytes` and
/// `auth_info_bytes`, and returns the body (and its encoding) to sign.
pub(crate) fn apply_extension_signer(
    signer: Option<&dyn ExtensionSigner>,
    request: ExtensionSignRequest<'_>,
    body: TxBody,
    body_bytes: Vec<u8>,
    messages: &[Any],
    memo: &Memo,
) -> Result<(TxBody, Vec<u8>), Error> {
    let Some(signer) = signer else {
        return Ok((body, body_bytes));
    };

    let added = signer
        .extension_options(&request)
        .map_err(|reason| Error::extension_signer(request.chain_id.clone(), reason))?;

    let mut extension_options = body.extension_options;
    extension_options.extend(added);

    crate::chain::cosmos::encode::tx_body_and_bytes(messages, memo, extension_options)
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use prost::Message;

    use super::*;
    use crate::chain::cosmos::encode::tx_body_and_bytes;

    #[derive(Debug, Default)]
    struct RecordingSigner {
        seen_body: Mutex<Vec<u8>>,
    }

    impl ExtensionSigner for RecordingSigner {
        fn extension_options(
            &self,
            request: &ExtensionSignRequest<'_>,
        ) -> Result<Vec<Any>, String> {
            *self.seen_body.lock().unwrap() = request.body_bytes.to_vec();
            Ok(vec![Any {
                type_url: "/example.v1.ExtraSignature".to_string(),
                value: vec![request.sequence as u8; 4],
            }])
        }
    }

    #[derive(Debug)]
    struct FailingSigner;

    impl ExtensionSigner for FailingSigner {
        fn extension_options(&self, _: &ExtensionSignRequest<'_>) -> Result<Vec<Any>, String> {
            Err("key not loaded".to_string())
        }
    }

    fn inputs() -> (ChainId, Vec<Any>, Memo, Vec<Any>) {
        let chain_id = ChainId::from_string("test-1");
        let messages = vec![Any {
            type_url: "/cosmos.bank.v1beta1.MsgSend".to_string(),
            value: vec![1, 2, 3],
        }];
        let static_option = Any {
            type_url: "/example.v1.StaticOption".to_string(),
            value: vec![9],
        };
        (
            chain_id,
            messages,
            Memo::new("memo").unwrap(),
            vec![static_option],
        )
    }

    fn request<'a>(chain_id: &'a ChainId, body_bytes: &'a [u8]) -> ExtensionSignRequest<'a> {
        ExtensionSignRequest {
            chain_id,
            body_bytes,
            auth_info_bytes: &[7, 7],
            account_number: 42,
            sequence: 5,
        }
    }

    #[test]
    fn without_a_signer_the_body_is_unchanged() {
        let (chain_id, messages, memo, options) = inputs();
        let (body, body_bytes) = tx_body_and_bytes(&messages, &memo, options).unwrap();

        let (out, out_bytes) = apply_extension_signer(
            None,
            request(&chain_id, &body_bytes),
            body.clone(),
            body_bytes.clone(),
            &messages,
            &memo,
        )
        .unwrap();

        assert_eq!(out, body);
        assert_eq!(out_bytes, body_bytes);
    }

    #[test]
    fn signer_sees_the_body_without_its_option_and_its_option_is_appended() {
        let (chain_id, messages, memo, options) = inputs();
        let (body, body_bytes) = tx_body_and_bytes(&messages, &memo, options).unwrap();
        let signer = RecordingSigner::default();

        let (out, out_bytes) = apply_extension_signer(
            Some(&signer),
            request(&chain_id, &body_bytes),
            body,
            body_bytes.clone(),
            &messages,
            &memo,
        )
        .unwrap();

        assert_eq!(*signer.seen_body.lock().unwrap(), body_bytes);
        let types: Vec<_> = out
            .extension_options
            .iter()
            .map(|a| a.type_url.as_str())
            .collect();
        assert_eq!(
            types,
            ["/example.v1.StaticOption", "/example.v1.ExtraSignature"]
        );
        assert_eq!(out.extension_options[1].value, vec![5; 4]);
        assert_eq!(out_bytes, out.encode_to_vec());
        assert_eq!(out.messages, messages);
    }

    #[test]
    fn signer_errors_stop_the_transaction() {
        let (chain_id, messages, memo, options) = inputs();
        let (body, body_bytes) = tx_body_and_bytes(&messages, &memo, options).unwrap();

        let err = apply_extension_signer(
            Some(&FailingSigner),
            request(&chain_id, &body_bytes),
            body,
            body_bytes.clone(),
            &messages,
            &memo,
        )
        .unwrap_err();

        assert!(err.to_string().contains("key not loaded"));
        assert!(err.to_string().contains("test-1"));
    }
}

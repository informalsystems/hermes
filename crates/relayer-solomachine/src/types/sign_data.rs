use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::Data as ProtoData;
use ibc_proto::cosmos::tx::signing::v1beta1::SignatureDescriptor as ProtoSignatureDescriptor;

use crate::methods::encode::public_key::{encode_public_key, PublicKey};

#[derive(Clone)]
pub struct SolomachineSignData {
    pub diversifier: String,
    pub sequence: u64,
    pub timestamp: u64,
    /// The `path` serves as the key for accessing the `data` field in the key-value store.
    pub path: Vec<u8>,
    /// The content stored at the `path` in the key-value store.
    pub data: Vec<u8>,
}

pub fn membership_sign_data(
    diversifier: &str,
    sequence: u64,
    timestamp: u64,
    path: &str,
    data: &[u8],
) -> SolomachineSignData {
    SolomachineSignData {
        diversifier: diversifier.to_string(),
        sequence,
        timestamp,
        path: path.into(),
        data: data.into(),
    }
}

pub fn non_membership_sign_data(
    diversifier: &str,
    sequence: u64,
    timestamp: u64,
    path: &str,
) -> SolomachineSignData {
    SolomachineSignData {
        diversifier: diversifier.to_string(),
        sequence,
        timestamp,
        path: path.into(),
        data: Vec::new(),
    }
}

#[derive(Clone)]
pub struct SolomachineTimestampedSignData {
    pub signature_data: SignatureDescriptor,
    pub timestamp: u64,
}

#[derive(Clone)]
pub struct SignatureDescriptor {
    pub public_key: PublicKey,
    pub data: Option<ProtoData>,
    pub sequence: u64,
}

impl From<SignatureDescriptor> for ProtoSignatureDescriptor {
    fn from(value: SignatureDescriptor) -> Self {
        //        let data = value.data.map(|v| v.into());
        let public_key = encode_public_key(&value.public_key);

        ProtoSignatureDescriptor {
            // TODO: Error decoding public key here:
            // https://github.com/cosmos/ibc-go/blob/v7.2.0/modules/light-clients/06-solomachine/client_state.go#L118
            // https://github.com/cosmos/cosmos-sdk/blob/v0.47.3/types/tx/signing/signing.pb.go#L1209
            public_key: Some(public_key),
            // TODO: Error after decoding data, when verifying signature:
            // https://github.com/cosmos/ibc-go/blob/v7.2.0/modules/light-clients/06-solomachine/client_state.go#L145
            // https://github.com/cosmos/ibc-go/blob/v7.2.0/modules/light-clients/06-solomachine/proof.go#L34
            //public_key: None,
            data: value.data,
            sequence: value.sequence,
        }
    }
}

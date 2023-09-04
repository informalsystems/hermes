use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::data::{Single, Sum};
use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::Data;
use ibc_proto::ibc::lightclients::tendermint::v1::ClientState as ProtoClientState;
use ibc_relayer_cosmos::methods::encode::encode_protobuf;
use ibc_relayer_cosmos::types::tendermint::TendermintClientState;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use prost::EncodeError;
use secp256k1::SecretKey;

use crate::methods::encode::public_key::PublicKey;
use crate::methods::encode::sign_data::sign_with_data;
use crate::types::client_state::SolomachineClientState;
use crate::types::sign_data::{
    SignatureDescriptor, SolomachineSignData, SolomachineTimestampedSignData,
};

// Create a sign data for the client state proof that the solomachine has
// the Tendermint client state of the counterparty Cosmos chain
pub fn client_state_proof_data(
    public_key: &PublicKey,
    secret_key: &SecretKey,
    solo_client_state: &SolomachineClientState,
    commitment_prefix: &str,
    client_id: &ClientId,
    cosmos_client_state: &TendermintClientState,
) -> Result<SolomachineTimestampedSignData, EncodeError> {
    let proto_client_state: ProtoClientState = cosmos_client_state.clone().into();

    let client_state_bytes = encode_protobuf(&proto_client_state)?;

    let path = format!("{commitment_prefix}clients/{client_id}/clientState");

    // Create SignData
    let sign_data = SolomachineSignData {
        diversifier: solo_client_state.consensus_state.diversifier.clone(),
        sequence: solo_client_state.sequence,
        timestamp: solo_client_state.consensus_state.timestamp,
        path: path.into(),
        data: client_state_bytes,
    };

    // Sign data using Secret Key
    let signed_data = sign_with_data(secret_key, &sign_data)?;

    let data = Data {
        sum: Some(Sum::Single(Single {
            mode: 2,
            signature: signed_data.serialize_compact().to_vec(),
        })),
    };

    let signature_data = SignatureDescriptor {
        public_key: public_key.clone(),
        data: Some(data),
        sequence: solo_client_state.sequence,
    };

    // Create Timestamped signed data
    let timestamped_signed_data = SolomachineTimestampedSignData {
        signature_data,
        timestamp: solo_client_state.consensus_state.timestamp,
    };

    Ok(timestamped_signed_data)
}

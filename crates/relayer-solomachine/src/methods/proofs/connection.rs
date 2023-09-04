use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::data::{Single, Sum};
use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::Data;
use ibc_proto::ibc::core::connection::v1::ConnectionEnd as ProtoConnectionEnd;
use ibc_relayer_cosmos::methods::encode::encode_protobuf;
use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use prost::EncodeError;
use secp256k1::SecretKey;

use crate::methods::encode::public_key::PublicKey;
use crate::methods::encode::sign_data::sign_with_data;
use crate::types::client_state::SolomachineClientState;
use crate::types::sign_data::{
    SignatureDescriptor, SolomachineSignData, SolomachineTimestampedSignData,
};

// Create a sign data for the connection proof that the solomachine has
// the connection end of the counterparty Cosmos chain
pub fn connection_proof_data(
    public_key: &PublicKey,
    secret_key: &SecretKey,
    client_state: &SolomachineClientState,
    commitment_prefix: &str,
    connection_id: &ConnectionId,
    connection_end: ConnectionEnd,
) -> Result<SolomachineTimestampedSignData, EncodeError> {
    let proto_connection_end: ProtoConnectionEnd = connection_end.into();

    let connection_end_bytes = encode_protobuf(&proto_connection_end)?;

    let path = format!("{commitment_prefix}connections/{connection_id}");

    // Create SignData
    let sign_data = SolomachineSignData {
        diversifier: client_state.consensus_state.diversifier.clone(),
        sequence: client_state.sequence,
        timestamp: client_state.consensus_state.timestamp,
        path: path.into(),
        data: connection_end_bytes,
    };

    // Sign data using Secret Key
    let signed_data = sign_with_data(secret_key, &sign_data)?;

    let data = Data {
        sum: Some(Sum::Single(Single {
            mode: 1,
            signature: signed_data.serialize_compact().to_vec(),
        })),
    };

    let signature_data = SignatureDescriptor {
        public_key: public_key.clone(),
        data: Some(data),
        sequence: client_state.sequence,
    };

    // Create Timestamped signed data
    let timestamped_signed_data = SolomachineTimestampedSignData {
        signature_data,
        timestamp: client_state.consensus_state.timestamp,
    };

    Ok(timestamped_signed_data)
}

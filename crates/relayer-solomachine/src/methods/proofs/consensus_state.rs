use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::data::{Single, Sum};
use ibc_proto::cosmos::tx::signing::v1beta1::signature_descriptor::Data;
use ibc_proto::ibc::lightclients::tendermint::v1::ConsensusState as ProtoConsensusState;
use ibc_relayer_cosmos::methods::encode::encode_protobuf;
use ibc_relayer_cosmos::types::tendermint::TendermintConsensusState;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::Height;
use prost::EncodeError;
use secp256k1::SecretKey;

use crate::methods::encode::sign_data::sign_with_data;
use crate::types::client_state::SolomachineClientState;
use crate::types::sign_data::{SolomachineSignData, SolomachineTimestampedSignData};

// Create a sign data for the consensus state proof that the solomachine has
// the Tendermint consensus state of the counterparty Cosmos chain
pub fn consensus_state_proof_data(
    secret_key: &SecretKey,
    solo_client_state: &SolomachineClientState,
    commitment_prefix: &str,
    client_id: &ClientId,
    height: Height,
    cosmos_client_state: &TendermintConsensusState,
) -> Result<SolomachineTimestampedSignData, EncodeError> {
    let proto_client_state: ProtoConsensusState = cosmos_client_state.clone().into();

    let client_state_bytes = encode_protobuf(&proto_client_state)?;

    let path = format!("{commitment_prefix}clients/{client_id}/consensusStates/{height}");

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
            mode: 0,
            signature: signed_data.serialize_compact().to_vec(),
        })),
    };

    let bytes_data = encode_protobuf(&data).unwrap();

    // Create Timestamped signed data
    let timestamped_signed_data = SolomachineTimestampedSignData {
        signature_data: bytes_data,
        timestamp: solo_client_state.consensus_state.timestamp,
    };

    Ok(timestamped_signed_data)
}

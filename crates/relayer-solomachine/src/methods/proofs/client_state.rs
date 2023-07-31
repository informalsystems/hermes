use ibc_proto::ibc::lightclients::tendermint::v1::ClientState as ProtoClientState;
use ibc_relayer_cosmos::methods::encode::encode_protobuf;
use ibc_relayer_cosmos::types::tendermint::TendermintClientState;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use prost::EncodeError;

use crate::types::client_state::SolomachineClientState;
use crate::types::sign_data::SolomachineSignData;

// Create a sign data for the client state proof that the solomachine has
// the Tendermint client state of the counterparty Cosmos chain
pub fn client_state_proof_data(
    solo_client_state: &SolomachineClientState,
    commitment_prefix: &str,
    client_id: &ClientId,
    cosmos_client_state: &TendermintClientState,
) -> Result<SolomachineSignData, EncodeError> {
    let proto_client_state: ProtoClientState = cosmos_client_state.clone().into();

    let client_state_bytes = encode_protobuf(&proto_client_state)?;

    let path = format!("{commitment_prefix}clients/{client_id}/clientState");

    let sign_data = SolomachineSignData {
        diversifier: solo_client_state.consensus_state.diversifier.clone(),
        sequence: solo_client_state.sequence,
        timestamp: solo_client_state.consensus_state.timestamp,
        path: path.into(),
        data: client_state_bytes,
    };

    Ok(sign_data)
}

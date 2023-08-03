use ibc_proto::ibc::lightclients::tendermint::v1::ConsensusState as ProtoConsensusState;
use ibc_relayer_cosmos::methods::encode::encode_protobuf;
use ibc_relayer_cosmos::types::tendermint::TendermintConsensusState;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use ibc_relayer_types::Height;
use prost::EncodeError;

use crate::types::client_state::SolomachineClientState;
use crate::types::sign_data::SolomachineSignData;

// Create a sign data for the consensus state proof that the solomachine has
// the Tendermint consensus state of the counterparty Cosmos chain
pub fn consensus_state_proof_data(
    solo_client_state: &SolomachineClientState,
    commitment_prefix: &str,
    client_id: &ClientId,
    height: Height,
    cosmos_client_state: &TendermintConsensusState,
) -> Result<SolomachineSignData, EncodeError> {
    let proto_client_state: ProtoConsensusState = cosmos_client_state.clone().into();

    let client_state_bytes = encode_protobuf(&proto_client_state)?;

    let path = format!("{commitment_prefix}clients/{client_id}/consensusStates/{height}");

    let sign_data = SolomachineSignData {
        diversifier: solo_client_state.consensus_state.diversifier.clone(),
        sequence: solo_client_state.sequence,
        timestamp: solo_client_state.consensus_state.timestamp,
        path: path.into(),
        data: client_state_bytes,
    };

    Ok(sign_data)
}

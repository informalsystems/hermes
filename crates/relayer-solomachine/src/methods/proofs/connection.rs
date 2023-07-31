use ibc_proto::ibc::core::connection::v1::ConnectionEnd as ProtoConnectionEnd;
use ibc_relayer_cosmos::methods::encode::encode_protobuf;
use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics24_host::identifier::ConnectionId;
use prost::EncodeError;

use crate::types::client_state::SolomachineClientState;
use crate::types::sign_data::SolomachineSignData;

// Create a sign data for the connection proof that the solomachine has
// the connection end of the counterparty Cosmos chain
pub fn connection_proof_data(
    client_state: &SolomachineClientState,
    commitment_prefix: &str,
    connection_id: &ConnectionId,
    connection_end: ConnectionEnd,
) -> Result<SolomachineSignData, EncodeError> {
    let proto_connection_end: ProtoConnectionEnd = connection_end.into();

    let connection_end_bytes = encode_protobuf(&proto_connection_end)?;

    let path = format!("{commitment_prefix}connections/{connection_id}");

    let sign_data = SolomachineSignData {
        diversifier: client_state.consensus_state.diversifier.clone(),
        sequence: client_state.sequence,
        timestamp: client_state.consensus_state.timestamp,
        path: path.into(),
        data: connection_end_bytes,
    };

    Ok(sign_data)
}

use crate::types::client_state::SolomachineClientState;
use crate::types::header::SolomachineHeader;

#[derive(Debug)]
pub struct SolomachineCreateClientPayload {
    pub client_state: SolomachineClientState,
}

pub struct SolomachineUpdateClientPayload {
    pub header: SolomachineHeader,
}

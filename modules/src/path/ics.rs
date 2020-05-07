use super::{ClientStatePath, ConnectionPath, ConsensusStatePath};

pub fn connection_path(path: &ConnectionPath) -> String {
    format!("connections/{}", path.connection_id)
}

pub fn consensus_state_path(path: &ConsensusStatePath) -> String {
    format!("clients/{}/consensusState/{}", path.client_id, path.height)
}

pub fn client_state_path(path: &ClientStatePath) -> String {
    format!("clients/{}/clientState", path.client_id)
}

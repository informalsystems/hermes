use super::{ConnectionPath, ConsensusStatePath};

pub fn connection_path(path: &ConnectionPath) -> String {
    format!("connection/{}", path.connection_id)
}

pub fn consensus_state_path(path: &ConsensusStatePath) -> String {
    format!("consensusState/{}/{}", path.client_id, path.height)
}

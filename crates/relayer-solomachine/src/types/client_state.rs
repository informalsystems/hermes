use crate::types::consensus_state::SolomachineConsensusState;

#[derive(Clone)]
pub struct SolomachineClientState {
    pub sequence: u64,
    pub is_frozen: bool,
    pub consensus_state: SolomachineConsensusState,
}

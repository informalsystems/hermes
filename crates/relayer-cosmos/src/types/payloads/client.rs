use crate::types::tendermint::{TendermintClientState, TendermintConsensusState, TendermintHeader};

pub struct CosmosUpdateClientPayload {
    pub headers: Vec<TendermintHeader>,
}

pub struct CosmosCreateClientPayload {
    pub client_state: TendermintClientState,
    pub consensus_state: TendermintConsensusState,
}

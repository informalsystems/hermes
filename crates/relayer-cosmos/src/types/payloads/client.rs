use crate::types::tendermint::{TendermintClientState, TendermintConsensusState, TendermintHeader};

#[derive(Debug)]
pub struct CosmosUpdateClientPayload {
    pub headers: Vec<TendermintHeader>,
}

#[derive(Debug)]
pub struct CosmosCreateClientPayload {
    pub client_state: TendermintClientState,
    pub consensus_state: TendermintConsensusState,
}

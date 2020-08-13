//! ICS 02: Client definitions

use crate::ics02_client::state::{ClientState, ConsensusState};

pub trait ClientDef {
    type Error: std::error::Error;

    type Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;

    fn new_client_state(_consensus_state: &Self::ConsensusState) -> Self::ClientState {
        todo!()
    }

    /// TODO
    fn check_validity_and_update_state(
        client_state: &mut Self::ClientState,
        consensus_state: &Self::ConsensusState,
        header: &Self::Header,
    ) -> Result<(), Self::Error>;
}


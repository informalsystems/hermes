//! ICS 02: Client definitions

use crate::ics02_client::state::{ClientState, ConsensusState};

pub trait ClientDef: Sized {
    type Error: std::error::Error;

    type Header;
    type ClientState: ClientState + From<Self::ConsensusState>;
    type ConsensusState: ConsensusState;

    /// TODO
    fn check_validity_and_update_state(
        client_state: &mut Self::ClientState,
        consensus_state: &Self::ConsensusState,
        header: &Self::Header,
    ) -> Result<(), Self::Error>;
}


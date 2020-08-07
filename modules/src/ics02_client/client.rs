//! ICS 02: Client definitions

use crate::ics02_client::state::{ClientState, ConsensusState};

pub trait ClientDef: Sized {
    type Header;
    type ClientState: ClientState + From<Self::ConsensusState>;
    type ConsensusState: ConsensusState;
}


//! ICS 02: Client definitions

use tendermint::lite::Height;
use tendermint::time::Time;

pub trait ClientDef: Sized {
    type Header: Header<Self>;
    type ClientState: ClientState<Self>;
    type ConsensusState: ConsensusState<Self>;
}

pub trait Header<CD: ClientDef> {}

pub trait ClientState<CD: ClientDef> {
    /// Initialise a client state with a provided consensus state.
    fn from_consensus_state(cs: CD::ConsensusState) -> Self;

    /// Height of most recent validated header.
    fn latest_client_height(&self) -> Height;
}

pub trait ConsensusState<CD: ClientDef> {
    /// Returns the timestamp associated with that consensus state.
    fn timestamp(&self) -> Time;
}

//! ICS 07: Tendermint Client

pub mod client_state;
pub mod consensus_state;
pub mod error;
pub mod header;
// pub mod msgs;

use tendermint::lite::Height;
use tendermint::time::Time;

use crate::ics02_client::client as ics02;

pub struct TendermintClient;

impl ics02::Header<TendermintClient> for header::Header {}

impl ics02::ClientState<TendermintClient> for client_state::ClientState {
    fn from_consensus_state(_cs: consensus_state::ConsensusState) -> Self {
        todo!()
    }

    fn latest_client_height(&self) -> Height {
        self.latest_header.signed_header.header.height.into()
    }
}

impl ics02::ConsensusState<TendermintClient> for consensus_state::ConsensusState {
    fn timestamp(&self) -> Time {
        self.timestamp
    }
}

impl ics02::ClientDef for TendermintClient {
    type Header = header::Header;
    type ClientState = client_state::ClientState;
    type ConsensusState = consensus_state::ConsensusState;
}


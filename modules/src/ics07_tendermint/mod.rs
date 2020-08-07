//! ICS 07: Tendermint Client

pub mod client_state;
pub mod consensus_state;
pub mod error;
pub mod header;
// pub mod msgs;

use crate::ics02_client::client as ics02;

pub struct TendermintClient;

impl ics02::ClientDef for TendermintClient {
    type Header = header::Header;
    type ClientState = client_state::ClientState;
    type ConsensusState = consensus_state::ConsensusState;
}


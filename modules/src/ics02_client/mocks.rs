#![allow(unreachable_code, unused_variables)]

/// TODO create new mock Client submodule, ala ics07-tendermint and move there
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader, ClientDef};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics23_commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};

use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::Height;

use crate::ics03_connection::connection::ConnectionEnd;
use serde_derive::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum MockError {}


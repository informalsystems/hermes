use serde_derive::{Deserialize, Serialize};

use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics23_commitment::CommitmentRoot;
use crate::ics24_host::identifier::ClientId;
use crate::Height;

use crate::ics02_client::mocks;
use crate::ics07_tendermint as tendermint;

pub trait ClientDef: Clone {
    type Header: Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)] // TODO: Add Eq
#[allow(clippy::large_enum_variant)]
pub enum AnyHeader {
    Mock(mocks::MockHeader),
    Tendermint(tendermint::header::Header),
}

impl Header for AnyHeader {
    fn height(&self) -> Height {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum AnyClientState {
    Mock(mocks::MockClientState),
}

impl ClientState for AnyClientState {
    fn client_id(&self) -> ClientId {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn get_latest_height(&self) -> Height {
        todo!()
    }

    fn is_frozen(&self) -> bool {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        _root: &CommitmentRoot,
    ) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum AnyConsensusState {
    Mock(mocks::MockConsensusState),
}

impl ConsensusState for AnyConsensusState {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }

    fn root(&self) -> &CommitmentRoot {
        todo!()
    }

    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnyClient {
    Mock(mocks::MockClient),
}

impl ClientDef for AnyClient {
    type Header = AnyHeader;
    type ClientState = AnyClientState;
    type ConsensusState = AnyConsensusState;
}


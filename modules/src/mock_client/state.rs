#![allow(unreachable_code, unused_variables)]
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

use tendermint_proto::DomainType;

use ibc_proto::ibc::mock::ClientState as RawMockClientState;
use ibc_proto::ibc::mock::ConsensusState as RawMockConsensusState;

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error::Error;
use crate::ics02_client::error::Kind;
use crate::ics02_client::header::Header;
use crate::ics02_client::state::{ClientState, ConsensusState};
use crate::ics23_commitment::commitment::CommitmentRoot;
use crate::mock_client::header::MockHeader;
use crate::Height;

/// A mock of an IBC client record as it is stored in a mock context.
/// For testing ICS02 handlers mostly, cf. `MockClientContext`.
#[derive(Clone, Debug)]
pub struct MockClientRecord {
    /// The type of this client.
    pub client_type: ClientType,
    /// The client state (representing only the latest height at the moment).
    pub client_state: MockClientState,
    /// Mapping of heights to consensus states for this client.
    pub consensus_states: HashMap<Height, MockConsensusState>,
}

/// A mock of a client state. For an example of a real structure that this mocks, you can see
/// `ClientState` of ics07_tendermint/client_state.rs.
/// TODO: `MockClientState` should evolve, at the very least needs a `is_frozen` boolean field.
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct MockClientState(pub MockHeader);

impl DomainType<RawMockClientState> for MockClientState {}

impl MockClientState {
    pub fn latest_height(&self) -> Height {
        (self.0).0
    }

    pub fn check_header_and_update_state(
        &self,
        header: AnyHeader,
    ) -> Result<(MockClientState, MockConsensusState), Box<dyn std::error::Error>> {
        match header {
            #[cfg(test)]
            AnyHeader::Mock(mock_header) => {
                if self.latest_height() >= header.height() {
                    return Err("header height is lower than client latest".into());
                }

                Ok((
                    MockClientState(mock_header),
                    MockConsensusState(mock_header),
                ))
            }
            _ => Err("bad header type for mock client state".into()),
        }
    }
}

impl From<MockClientState> for AnyClientState {
    fn from(mcs: MockClientState) -> Self {
        Self::Mock(mcs)
    }
}

impl TryFrom<RawMockClientState> for MockClientState {
    type Error = Error;

    fn try_from(raw: RawMockClientState) -> Result<Self, Self::Error> {
        Ok(MockClientState(raw.header.unwrap().try_into()?))
    }
}

impl From<MockClientState> for RawMockClientState {
    fn from(value: MockClientState) -> Self {
        RawMockClientState {
            header: Some(ibc_proto::ibc::mock::Header {
                height: Some(value.0.height().into()),
            }),
        }
    }
}

impl ClientState for MockClientState {
    fn chain_id(&self) -> String {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Mock
    }

    fn latest_height(&self) -> Height {
        self.0.height()
    }

    fn is_frozen(&self) -> bool {
        // TODO
        false
    }
}

impl From<MockConsensusState> for MockClientState {
    fn from(cs: MockConsensusState) -> Self {
        Self(cs.0)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MockConsensusState(pub MockHeader);

impl DomainType<RawMockConsensusState> for MockConsensusState {}

impl TryFrom<RawMockConsensusState> for MockConsensusState {
    type Error = Error;

    fn try_from(raw: RawMockConsensusState) -> Result<Self, Self::Error> {
        let raw_header = raw
            .header
            .ok_or_else(|| Kind::InvalidRawConsensusState.context("missing header"))?;

        Ok(Self(MockHeader::try_from(raw_header)?))
    }
}

impl From<MockConsensusState> for RawMockConsensusState {
    fn from(value: MockConsensusState) -> Self {
        RawMockConsensusState {
            header: Some(ibc_proto::ibc::mock::Header {
                height: Some(value.0.height().into()),
            }),
        }
    }
}

#[cfg(test)]
impl From<MockConsensusState> for AnyConsensusState {
    fn from(mcs: MockConsensusState) -> Self {
        Self::Mock(mcs)
    }
}

impl ConsensusState for MockConsensusState {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn root(&self) -> &CommitmentRoot {
        todo!()
    }

    fn validate_basic(&self) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }
}

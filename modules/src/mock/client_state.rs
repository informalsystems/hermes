use crate::prelude::*;
use crate::test_utils::Crypto;

use alloc::collections::btree_map::BTreeMap as HashMap;

use core::convert::Infallible;
use core::fmt::Debug;
use core::time::Duration;

use serde::{Deserialize, Serialize};
use tendermint_proto::Protobuf;

use crate::clients::crypto_ops::crypto::CryptoOps;
use ibc_proto::ibc::mock::ClientState as RawMockClientState;
use ibc_proto::ibc::mock::ConsensusState as RawMockConsensusState;

use crate::core::ics02_client::client_consensus::{AnyConsensusState, ConsensusState};
use crate::core::ics02_client::client_state::{AnyClientState, ClientState};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentRoot;
use crate::core::ics24_host::identifier::ChainId;
use crate::mock::header::MockHeader;
use crate::timestamp::Timestamp;
use crate::Height;

/// A mock of an IBC client record as it is stored in a mock context.
/// For testing ICS02 handlers mostly, cf. `MockClientContext`.
#[derive(Clone, Debug)]
pub struct MockClientRecord {
    /// The type of this client.
    pub client_type: ClientType,

    /// The client state (representing only the latest height at the moment).
    pub client_state: Option<AnyClientState>,

    /// Mapping of heights to consensus states for this client.
    pub consensus_states: HashMap<Height, AnyConsensusState<Crypto>>,
}

/// A mock of a client state. For an example of a real structure that this mocks, you can see
/// `ClientState` of ics07_tendermint/client_state.rs.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockClientState {
    pub header: MockHeader,
    pub frozen_height: Option<Height>,
}

impl Protobuf<RawMockClientState> for MockClientState {}

impl MockClientState {
    pub fn new(header: MockHeader) -> Self {
        Self {
            header,
            frozen_height: None,
        }
    }

    pub fn latest_height(&self) -> Height {
        self.header.height()
    }

    pub fn refresh_time(&self) -> Option<Duration> {
        None
    }

    pub fn expired(&self, _elapsed: Duration) -> bool {
        false
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
        Ok(Self::new(raw.header.unwrap().try_into()?))
    }
}

impl From<MockClientState> for RawMockClientState {
    fn from(value: MockClientState) -> Self {
        RawMockClientState {
            header: Some(ibc_proto::ibc::mock::Header {
                height: Some(value.header.height().into()),
                timestamp: value.header.timestamp.nanoseconds(),
            }),
        }
    }
}

impl ClientState for MockClientState {
    type UpgradeOptions = ();

    fn chain_id(&self) -> ChainId {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Mock
    }

    fn latest_height(&self) -> Height {
        self.header.height()
    }

    fn frozen_height(&self) -> Option<Height> {
        self.frozen_height
    }

    fn upgrade(self, _upgrade_height: Height, _upgrade_options: (), _chain_id: ChainId) -> Self {
        todo!()
    }

    fn wrap_any(self) -> AnyClientState {
        AnyClientState::Mock(self)
    }
}

impl<Crypto> From<MockConsensusState<Crypto>> for MockClientState {
    fn from(cs: MockConsensusState<Crypto>) -> Self {
        Self::new(cs.header)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MockConsensusState<Crypto> {
    pub header: MockHeader,
    pub root: CommitmentRoot,
    _phantom: core::marker::PhantomData<Crypto>,
}

impl<Crypto> MockConsensusState<Crypto> {
    pub fn new(header: MockHeader) -> Self {
        MockConsensusState {
            header,
            root: CommitmentRoot::from(vec![0]),
            _phantom: Default::default(),
        }
    }

    pub fn timestamp(&self) -> Timestamp {
        self.header.timestamp
    }
}

impl<Crypto: Clone> Protobuf<RawMockConsensusState> for MockConsensusState<Crypto> {}

impl<Crypto: Clone> TryFrom<RawMockConsensusState> for MockConsensusState<Crypto> {
    type Error = Error;

    fn try_from(raw: RawMockConsensusState) -> Result<Self, Self::Error> {
        let raw_header = raw.header.ok_or_else(Error::missing_raw_consensus_state)?;

        Ok(Self {
            header: MockHeader::try_from(raw_header)?,
            root: CommitmentRoot::from(vec![0]),
            _phantom: Default::default(),
        })
    }
}

impl<Crypto: Clone> From<MockConsensusState<Crypto>> for RawMockConsensusState {
    fn from(value: MockConsensusState<Crypto>) -> Self {
        RawMockConsensusState {
            header: Some(ibc_proto::ibc::mock::Header {
                height: Some(value.header.height().into()),
                timestamp: value.header.timestamp.nanoseconds(),
            }),
        }
    }
}

impl<Crypto> From<MockConsensusState<Crypto>> for AnyConsensusState<Crypto> {
    fn from(mcs: MockConsensusState<Crypto>) -> Self {
        Self::Mock(mcs)
    }
}

impl<Crypto: Debug + Clone + Send + Sync + CryptoOps> ConsensusState
    for MockConsensusState<Crypto>
{
    type Error = Infallible;
    type Crypto = Crypto;

    fn client_type(&self) -> ClientType {
        ClientType::Mock
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn wrap_any(self) -> AnyConsensusState<Crypto> {
        AnyConsensusState::Mock(self)
    }
}

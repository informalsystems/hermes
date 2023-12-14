use ibc_proto::{
    google::protobuf::Any,
    ibc::mock::ConsensusState as RawMockConsensusState,
    Protobuf,
};
use serde::{
    Deserialize,
    Serialize,
};

use crate::{
    core::{
        ics02_client::{
            client_type::ClientType,
            consensus_state::ConsensusState,
            error::Error,
        },
        ics23_commitment::commitment::CommitmentRoot,
    },
    mock::header::MockHeader,
    timestamp::Timestamp,
};

pub const MOCK_CONSENSUS_STATE_TYPE_URL: &str = "/ibc.mock.ConsensusState";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockConsensusState {
    pub header: MockHeader,
    pub root: CommitmentRoot,
}

impl MockConsensusState {
    pub fn new(header: MockHeader) -> Self {
        MockConsensusState {
            header,
            root: CommitmentRoot::from(vec![0]),
        }
    }

    pub fn timestamp(&self) -> Timestamp {
        self.header.timestamp
    }
}

impl Protobuf<RawMockConsensusState> for MockConsensusState {}

impl TryFrom<RawMockConsensusState> for MockConsensusState {
    type Error = Error;

    fn try_from(raw: RawMockConsensusState) -> Result<Self, Self::Error> {
        let raw_header = raw.header.ok_or_else(Error::missing_raw_consensus_state)?;

        Ok(Self {
            header: MockHeader::try_from(raw_header)?,
            root: CommitmentRoot::from(vec![0]),
        })
    }
}

impl From<MockConsensusState> for RawMockConsensusState {
    fn from(value: MockConsensusState) -> Self {
        RawMockConsensusState {
            header: Some(ibc_proto::ibc::mock::Header {
                height: Some(value.header.height().into()),
                timestamp: value.header.timestamp.nanoseconds(),
            }),
        }
    }
}

impl Protobuf<Any> for MockConsensusState {}

impl TryFrom<Any> for MockConsensusState {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        use core::ops::Deref;

        use bytes::Buf;
        use prost::Message;

        fn decode_consensus_state<B: Buf>(buf: B) -> Result<MockConsensusState, Error> {
            RawMockConsensusState::decode(buf)
                .map_err(Error::decode)?
                .try_into()
        }

        match raw.type_url.as_str() {
            MOCK_CONSENSUS_STATE_TYPE_URL => {
                decode_consensus_state(raw.value.deref()).map_err(Into::into)
            }
            _ => Err(Error::unknown_consensus_state_type(raw.type_url)),
        }
    }
}

impl From<MockConsensusState> for Any {
    fn from(consensus_state: MockConsensusState) -> Self {
        Any {
            type_url: MOCK_CONSENSUS_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawMockConsensusState>::encode_vec(consensus_state),
        }
    }
}

impl ConsensusState for MockConsensusState {
    fn client_type(&self) -> ClientType {
        ClientType::Mock
    }

    fn root(&self) -> &CommitmentRoot {
        &self.root
    }

    fn timestamp(&self) -> Timestamp {
        self.header.timestamp
    }
}

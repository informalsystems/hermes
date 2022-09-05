use crate::core::ics02_client::context::ClientReader;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::context::ChannelReader;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics23_commitment::merkle::apply_prefix;
use crate::core::ics24_host::path::ClientConsensusStatePath;
use crate::core::ics24_host::Path;
use crate::prelude::*;

use alloc::collections::btree_map::BTreeMap as HashMap;
use core::time::Duration;
use dyn_clone::clone_box;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::mock::ClientState as RawMockClientState;
use ibc_proto::protobuf::Protobuf;
use serde::{Deserialize, Serialize};

use crate::core::ics02_client::client_state::{ClientState, UpdatedState, UpgradeOptions};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState;
use crate::core::ics02_client::error::Error;
use crate::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use crate::mock::consensus_state::MockConsensusState;
use crate::mock::header::MockHeader;
use crate::Height;

pub const MOCK_CLIENT_STATE_TYPE_URL: &str = "/ibc.mock.ClientState";

/// A mock of an IBC client record as it is stored in a mock context.
/// For testing ICS02 handlers mostly, cf. `MockClientContext`.
#[derive(Clone, Debug)]
pub struct MockClientRecord {
    /// The type of this client.
    pub client_type: ClientType,

    /// The client state (representing only the latest height at the moment).
    pub client_state: Option<Box<dyn ClientState>>,

    /// Mapping of heights to consensus states for this client.
    pub consensus_states: HashMap<Height, Box<dyn ConsensusState>>,
}

/// A mock of a client state. For an example of a real structure that this mocks, you can see
/// `ClientState` of ics07_tendermint/client_state.rs.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MockClientState {
    pub header: MockHeader,
    pub frozen_height: Option<Height>,
}

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
}

impl Protobuf<RawMockClientState> for MockClientState {}

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

impl Protobuf<Any> for MockClientState {}

impl TryFrom<Any> for MockClientState {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Error> {
        use bytes::Buf;
        use core::ops::Deref;
        use prost::Message;

        fn decode_client_state<B: Buf>(buf: B) -> Result<MockClientState, Error> {
            RawMockClientState::decode(buf)
                .map_err(Error::decode)?
                .try_into()
        }

        match raw.type_url.as_str() {
            MOCK_CLIENT_STATE_TYPE_URL => {
                decode_client_state(raw.value.deref()).map_err(Into::into)
            }
            _ => Err(Error::unknown_client_state_type(raw.type_url)),
        }
    }
}

impl From<MockClientState> for Any {
    fn from(client_state: MockClientState) -> Self {
        Any {
            type_url: MOCK_CLIENT_STATE_TYPE_URL.to_string(),
            value: Protobuf::<RawMockClientState>::encode_vec(&client_state)
                .expect("encoding to `Any` from `MockClientState`"),
        }
    }
}

impl ClientState for MockClientState {
    fn chain_id(&self) -> ChainId {
        unimplemented!()
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

    fn upgrade(
        &mut self,
        _upgrade_height: Height,
        _upgrade_options: &dyn UpgradeOptions,
        _chain_id: ChainId,
    ) {
        unimplemented!()
    }

    fn expired(&self, _elapsed: Duration) -> bool {
        false
    }

    fn initialise(&self, consensus_state: Any) -> Result<Box<dyn ConsensusState>, Error> {
        MockConsensusState::try_from(consensus_state).map(MockConsensusState::into_box)
    }

    fn check_header_and_update_state(
        &self,
        _ctx: &dyn ClientReader,
        _client_id: ClientId,
        header: Any,
    ) -> Result<UpdatedState, Error> {
        let header = MockHeader::try_from(header)?;

        if self.latest_height() >= header.height() {
            return Err(Error::low_header_height(
                header.height(),
                self.latest_height(),
            ));
        }

        Ok(UpdatedState {
            client_state: MockClientState::new(header).into_box(),
            consensus_state: MockConsensusState::new(header).into_box(),
        })
    }

    fn verify_upgrade_and_update_state(
        &self,
        consensus_state: Any,
        _proof_upgrade_client: MerkleProof,
        _proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<UpdatedState, Error> {
        let consensus_state = MockConsensusState::try_from(consensus_state)?;
        Ok(UpdatedState {
            client_state: clone_box(self),
            consensus_state: consensus_state.into_box(),
        })
    }

    fn verify_client_consensus_state(
        &self,
        _height: Height,
        prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        _expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Error> {
        let client_prefixed_path = Path::ClientConsensusState(ClientConsensusStatePath {
            client_id: client_id.clone(),
            epoch: consensus_height.revision_number(),
            height: consensus_height.revision_height(),
        })
        .to_string();

        let _path = apply_prefix(prefix, vec![client_prefixed_path]);

        Ok(())
    }

    fn verify_connection_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _connection_id: &ConnectionId,
        _expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_channel_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_client_full_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _client_id: &ClientId,
        _expected_client_state: Any,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_packet_data(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
        _commitment: PacketCommitment,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_packet_acknowledgement(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
        _ack: AcknowledgementCommitment,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_next_sequence_recv(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_packet_receipt_absence(
        &self,
        _ctx: &dyn ChannelReader,
        _height: Height,
        _connection_end: &ConnectionEnd,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _port_id: &PortId,
        _channel_id: &ChannelId,
        _sequence: Sequence,
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl From<MockConsensusState> for MockClientState {
    fn from(cs: MockConsensusState) -> Self {
        Self::new(cs.header)
    }
}

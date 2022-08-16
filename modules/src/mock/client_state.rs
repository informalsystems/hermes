use crate::prelude::*;

use alloc::collections::btree_map::BTreeMap as HashMap;
use core::time::Duration;

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::mock::ClientState as RawMockClientState;
use ibc_proto::protobuf::Protobuf;
use serde::{Deserialize, Serialize};

use crate::core::ics02_client::client_state::{ClientState, UpgradeOptions};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::consensus_state::ConsensusState;
use crate::core::ics02_client::error::Error;
use crate::core::ics24_host::identifier::ChainId;
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

    fn upgrade(
        &mut self,
        _upgrade_height: Height,
        _upgrade_options: &dyn UpgradeOptions,
        _chain_id: ChainId,
    ) {
        todo!()
    }

    fn expired(&self, _elapsed: Duration) -> bool {
        false
    }

    fn initialise(&self, consensus_state: Any) -> Result<Box<dyn ConsensusState>, Error> {
        todo!()
    }

    fn check_header_and_update_state(
        &self,
        ctx: &dyn crate::core::ics02_client::context::ClientReader,
        client_id: crate::core::ics24_host::identifier::ClientId,
        header: Any,
    ) -> Result<crate::core::ics02_client::client_state::UpdatedState, Error> {
        todo!()
    }

    fn verify_upgrade_and_update_state(
        &self,
        consensus_state: Any,
        proof_upgrade_client: crate::core::ics23_commitment::merkle::MerkleProof,
        proof_upgrade_consensus_state: crate::core::ics23_commitment::merkle::MerkleProof,
    ) -> Result<crate::core::ics02_client::client_state::UpdatedState, Error> {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        height: Height,
        prefix: &crate::core::ics23_commitment::commitment::CommitmentPrefix,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        consensus_height: Height,
        expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_connection_state(
        &self,
        height: Height,
        prefix: &crate::core::ics23_commitment::commitment::CommitmentPrefix,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        connection_id: &crate::core::ics24_host::identifier::ConnectionId,
        expected_connection_end: &crate::core::ics03_connection::connection::ConnectionEnd,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_channel_state(
        &self,
        height: Height,
        prefix: &crate::core::ics23_commitment::commitment::CommitmentPrefix,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        port_id: &crate::core::ics24_host::identifier::PortId,
        channel_id: &crate::core::ics24_host::identifier::ChannelId,
        expected_channel_end: &crate::core::ics04_channel::channel::ChannelEnd,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_client_full_state(
        &self,
        height: Height,
        prefix: &crate::core::ics23_commitment::commitment::CommitmentPrefix,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        expected_client_state: Any,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_packet_data(
        &self,
        ctx: &dyn crate::core::ics04_channel::context::ChannelReaderLightClient,
        height: Height,
        connection_end: &crate::core::ics03_connection::connection::ConnectionEnd,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        port_id: &crate::core::ics24_host::identifier::PortId,
        channel_id: &crate::core::ics24_host::identifier::ChannelId,
        sequence: crate::core::ics04_channel::packet::Sequence,
        commitment: crate::core::ics04_channel::commitment::PacketCommitment,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn crate::core::ics04_channel::context::ChannelReaderLightClient,
        height: Height,
        connection_end: &crate::core::ics03_connection::connection::ConnectionEnd,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        port_id: &crate::core::ics24_host::identifier::PortId,
        channel_id: &crate::core::ics24_host::identifier::ChannelId,
        sequence: crate::core::ics04_channel::packet::Sequence,
        ack: crate::core::ics04_channel::commitment::AcknowledgementCommitment,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn crate::core::ics04_channel::context::ChannelReaderLightClient,
        height: Height,
        connection_end: &crate::core::ics03_connection::connection::ConnectionEnd,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        port_id: &crate::core::ics24_host::identifier::PortId,
        channel_id: &crate::core::ics24_host::identifier::ChannelId,
        sequence: crate::core::ics04_channel::packet::Sequence,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn crate::core::ics04_channel::context::ChannelReaderLightClient,
        height: Height,
        connection_end: &crate::core::ics03_connection::connection::ConnectionEnd,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        port_id: &crate::core::ics24_host::identifier::PortId,
        channel_id: &crate::core::ics24_host::identifier::ChannelId,
        sequence: crate::core::ics04_channel::packet::Sequence,
    ) -> Result<(), Error> {
        todo!()
    }
}

impl From<MockConsensusState> for MockClientState {
    fn from(cs: MockConsensusState) -> Self {
        Self::new(cs.header)
    }
}

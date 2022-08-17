#![no_std]
#![deny(
    warnings,
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_qualifications,
    rust_2018_idioms,
    clippy::unwrap_used
)]
#![forbid(unsafe_code)]

extern crate alloc;

use alloc::boxed::Box;
use core::time::Duration;

use ibc::core::ics02_client::client_state::{ClientState, UpdatedState, UpgradeOptions};
use ibc::core::ics02_client::client_type::ClientType;
use ibc::core::ics02_client::consensus_state::ConsensusState;
use ibc::core::ics02_client::context::ClientReader;
use ibc::core::ics02_client::error::Error;
use ibc::core::ics02_client::header::Header;
use ibc::core::ics02_client::misbehaviour::Misbehaviour;
use ibc::core::ics03_connection::connection::ConnectionEnd;
use ibc::core::ics04_channel::channel::ChannelEnd;
use ibc::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use ibc::core::ics04_channel::context::ChannelReader;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, ConnectionId, PortId};
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::commitment::v1::MerkleProof;
use ibc_proto::protobuf::Protobuf;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ExtClientState;

impl Protobuf<Any> for ExtClientState {}

impl TryFrom<Any> for ExtClientState {
    type Error = Error;

    fn try_from(_value: Any) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl From<ExtClientState> for Any {
    fn from(_: ExtClientState) -> Self {
        todo!()
    }
}

impl ClientState for ExtClientState {
    fn chain_id(&self) -> ChainId {
        todo!()
    }

    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn latest_height(&self) -> Height {
        todo!()
    }

    fn frozen_height(&self) -> Option<Height> {
        todo!()
    }

    fn expired(&self, _elapsed: Duration) -> bool {
        todo!()
    }

    fn upgrade(
        &mut self,
        _upgrade_height: Height,
        _upgrade_options: &dyn UpgradeOptions,
        _chain_id: ChainId,
    ) {
        todo!()
    }

    fn initialise(&self, _consensus_state: Any) -> Result<Box<dyn ConsensusState>, Error> {
        todo!()
    }

    fn check_header_and_update_state(
        &self,
        _ctx: &dyn ClientReader,
        _client_id: ClientId,
        _header: Any,
    ) -> Result<UpdatedState, Error> {
        todo!()
    }

    fn verify_upgrade_and_update_state(
        &self,
        _consensus_state: Any,
        _proof_upgrade_client: MerkleProof,
        _proof_upgrade_consensus_state: MerkleProof,
    ) -> Result<UpdatedState, Error> {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _client_id: &ClientId,
        _consensus_height: Height,
        _expected_consensus_state: &dyn ConsensusState,
    ) -> Result<(), Error> {
        todo!()
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
        todo!()
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
        todo!()
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
        todo!()
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
        todo!()
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
        todo!()
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
        todo!()
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
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ExtHeader;

impl Protobuf<Any> for ExtHeader {}

impl TryFrom<Any> for ExtHeader {
    type Error = Error;

    fn try_from(_value: Any) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl From<ExtHeader> for Any {
    fn from(_: ExtHeader) -> Self {
        todo!()
    }
}

impl Header for ExtHeader {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }

    fn timestamp(&self) -> Timestamp {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ExtConsensusState;

impl Protobuf<Any> for ExtConsensusState {}

impl TryFrom<Any> for ExtConsensusState {
    type Error = Error;

    fn try_from(_value: Any) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl From<ExtConsensusState> for Any {
    fn from(_: ExtConsensusState) -> Self {
        todo!()
    }
}

impl ConsensusState for ExtConsensusState {
    fn client_type(&self) -> ClientType {
        todo!()
    }

    fn root(&self) -> &CommitmentRoot {
        todo!()
    }

    fn timestamp(&self) -> Timestamp {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ExtMisbehaviour;

impl Misbehaviour for ExtMisbehaviour {
    fn client_id(&self) -> &ClientId {
        todo!()
    }

    fn height(&self) -> Height {
        todo!()
    }
}

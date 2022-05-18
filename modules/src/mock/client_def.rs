use crate::clients::crypto_ops::crypto::CryptoOps;
use crate::core::ics02_client::client_consensus::AnyConsensusState;
use crate::core::ics02_client::client_def::{ClientDef, ConsensusUpdateResult};
use crate::core::ics02_client::client_state::AnyClientState;
use crate::core::ics02_client::error::Error;
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics23_commitment::merkle::apply_prefix;
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::core::ics24_host::path::ClientConsensusStatePath;
use crate::core::ics24_host::Path;
use crate::core::ics26_routing::context::LightClientContext;
use crate::mock::client_state::{MockClientState, MockConsensusState};
use crate::mock::header::MockHeader;
use crate::prelude::*;
use crate::Height;
use core::fmt::Debug;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockClient<Crypto>(core::marker::PhantomData<Crypto>);

impl<Crypto> Default for MockClient<Crypto> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<Crypto: CryptoOps + Debug + Send + Sync + PartialEq + Eq> ClientDef for MockClient<Crypto> {
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState<Self::Crypto>;
    type Crypto = Crypto;

    fn update_state(
        &self,
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult<Self::Crypto>), Error> {
        if client_state.latest_height() >= header.height() {
            return Err(Error::low_header_height(
                header.height(),
                client_state.latest_height(),
            ));
        }

        Ok((
            MockClientState::new(header),
            ConsensusUpdateResult::Single(AnyConsensusState::Mock(MockConsensusState::new(header))),
        ))
    }

    fn verify_client_consensus_state(
        &self,
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_state: &Self::ClientState,
        _height: Height,
        prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        _expected_consensus_state: &AnyConsensusState<Self::Crypto>,
    ) -> Result<(), Error> {
        let client_prefixed_path = Path::ClientConsensusState(ClientConsensusStatePath {
            client_id: client_id.clone(),
            epoch: consensus_height.revision_number,
            height: consensus_height.revision_height,
        })
        .to_string();

        let _path = apply_prefix(prefix, vec![client_prefixed_path]);

        Ok(())
    }

    fn verify_connection_state(
        &self,
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: &ClientId,
        _client_state: &Self::ClientState,
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
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: &ClientId,
        _client_state: &Self::ClientState,
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
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProofBytes,
        _root: &CommitmentRoot,
        _client_id: &ClientId,
        _expected_client_state: &AnyClientState,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn verify_packet_data(
        &self,
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: &ClientId,
        _client_state: &Self::ClientState,
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
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: &ClientId,
        _client_state: &Self::ClientState,
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
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: &ClientId,
        _client_state: &Self::ClientState,
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
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: &ClientId,
        _client_state: &Self::ClientState,
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

    fn verify_upgrade_and_update_state(
        &self,
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
        _proof_upgrade_client: Vec<u8>,
        _proof_upgrade_consensus_state: Vec<u8>,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult<Self::Crypto>), Error> {
        Ok((
            *client_state,
            ConsensusUpdateResult::Single(AnyConsensusState::Mock(consensus_state.clone())),
        ))
    }

    fn verify_header(
        &self,
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: ClientId,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn update_state_on_misbehaviour(
        &self,
        client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<Self::ClientState, Error> {
        Ok(client_state)
    }

    fn check_for_misbehaviour(
        &self,
        _ctx: &dyn LightClientContext<Crypto = Self::Crypto>,
        _client_id: ClientId,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<bool, Error> {
        Ok(false)
    }
}

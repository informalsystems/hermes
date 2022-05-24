use crate::core::ics02_client::client_def::ClientDef;

use super::client_state::NearClientState;
use super::consensus_state::NearConsensusState;
use super::crypto_ops::NearCryptoOps;
use super::error::Error;
use super::header::NearHeader;

#[derive(Debug, Clone)]
pub struct NearClient {}

impl ClientDef for NearClient {
    /// The data that we need to update the [`ClientState`] to a new block height
    type Header = NearHeader;

    /// The data that we need to know, to validate incoming headers and update the state
    /// of our [`ClientState`]. Ususally this will store:
    ///    - The current epoch
    ///    - The current validator set
    ///
    /// ```rust,no_run
    /// pub struct NearLightClientState {
    ///     head: LightClientBlockView,
    ///     current_validators: Vec<ValidatorStakeView>,
    ///     next_validators:  Vec<ValidatorStakeView>,
    /// }
    /// ```
    type ClientState = NearClientState;

    /// This is usually just two things, that should be derived from the header:
    ///    - The ibc commitment root hash as described by ics23 (possibly from tx outcome/ state proof)
    ///    - The timestamp of the header.
    type ConsensusState = NearConsensusState;

    type Crypto = NearCryptoOps;

    // rehydrate client from its own storage, then call this function
    fn verify_header(
        &self,
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: crate::core::ics24_host::identifier::ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(), Error> {
        // your light client, shouldn't do storage anymore, it should just do verification here.
        todo!()
    }

    fn update_state(
        &self,
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: crate::core::ics24_host::identifier::ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<
        (
            Self::ClientState,
            crate::core::ics02_client::client_def::ConsensusUpdateResult<Self::Crypto>,
        ),
        Error,
    > {
        // 1. create new client state from this header, return that.
        // 2. as well as all the neccessary consensus states.
        //
        //
        // []--[]--[]--[]--[]--[]--[]--[]--[]--[]
        // 11  12  13  14  15  16  17  18  19  20 <- block merkle root
        // ^                                    ^
        // |    <-------consensus states----->  |
        // current state                       new state
    }

    fn update_state_on_misbehaviour(
        &self,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<Self::ClientState, Error> {
        todo!()
    }

    fn check_for_misbehaviour(
        &self,
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: crate::core::ics24_host::identifier::ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<bool, Error> {
        todo!()
    }

    fn verify_upgrade_and_update_state(
        &self,
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
        proof_upgrade_client: Vec<u8>,
        proof_upgrade_consensus_state: Vec<u8>,
    ) -> Result<
        (
            Self::ClientState,
            crate::core::ics02_client::client_def::ConsensusUpdateResult<Self::Crypto>,
        ),
        Error,
    > {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_state: &Self::ClientState,
        height: crate::Height,
        prefix: &crate::core::ics23_commitment::commitment::CommitmentPrefix,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        consensus_height: crate::Height,
        expected_consensus_state: &crate::core::ics02_client::client_consensus::AnyConsensusState<
            Self::Crypto,
        >,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_connection_state(
        &self,
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        client_state: &Self::ClientState,
        height: crate::Height,
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
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        client_state: &Self::ClientState,
        height: crate::Height,
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
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_state: &Self::ClientState,
        height: crate::Height,
        prefix: &crate::core::ics23_commitment::commitment::CommitmentPrefix,
        proof: &crate::core::ics23_commitment::commitment::CommitmentProofBytes,
        root: &crate::core::ics23_commitment::commitment::CommitmentRoot,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        expected_client_state: &crate::core::ics02_client::client_state::AnyClientState,
    ) -> Result<(), Error> {
        todo!()
    }

    fn verify_packet_data(
        &self,
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        client_state: &Self::ClientState,
        height: crate::Height,
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
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        client_state: &Self::ClientState,
        height: crate::Height,
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
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        client_state: &Self::ClientState,
        height: crate::Height,
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
        ctx: &dyn crate::core::ics26_routing::context::LightClientContext<Crypto = Self::Crypto>,
        client_id: &crate::core::ics24_host::identifier::ClientId,
        client_state: &Self::ClientState,
        height: crate::Height,
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

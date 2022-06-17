use crate::clients::host_functions::HostFunctionsProvider;
use crate::clients::ics07_tendermint::client_def::TendermintClient;
#[cfg(any(test, feature = "ics11_beefy"))]
use crate::clients::ics11_beefy::client_def::BeefyClient;
use crate::core::ics02_client::client_consensus::{AnyConsensusState, ConsensusState};
use crate::core::ics02_client::client_state::{AnyClientState, ClientState};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::error::Error;
use crate::core::ics02_client::header::{AnyHeader, Header};
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics04_channel::channel::ChannelEnd;
use crate::core::ics04_channel::commitment::{AcknowledgementCommitment, PacketCommitment};
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics23_commitment::commitment::{
    CommitmentPrefix, CommitmentProofBytes, CommitmentRoot,
};
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use crate::core::ics26_routing::context::ReaderContext;
use crate::downcast;
use crate::prelude::*;
use crate::Height;
use core::fmt::Debug;

#[cfg(any(test, feature = "mocks"))]
use crate::mock::client_def::MockClient;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ConsensusUpdateResult {
    Single(AnyConsensusState),
    Batch(Vec<(Height, AnyConsensusState)>),
}

pub trait ClientDef: Clone {
    type Header: Header;
    type ClientState: ClientState;
    type ConsensusState: ConsensusState;

    fn verify_header(
        &self,
        ctx: &dyn ReaderContext,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(), Error>;

    fn update_state(
        &self,
        ctx: &dyn ReaderContext,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error>;

    fn update_state_on_misbehaviour(
        &self,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<Self::ClientState, Error>;

    fn check_for_misbehaviour(
        &self,
        ctx: &dyn ReaderContext,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<bool, Error>;

    /// TODO
    fn verify_upgrade_and_update_state(
        &self,
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
        proof_upgrade_client: Vec<u8>,
        proof_upgrade_consensus_state: Vec<u8>,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error>;

    /// Verification functions as specified in:
    /// <https://github.com/cosmos/ibc/tree/master/spec/core/ics-002-client-semantics>
    ///
    /// Verify a `proof` that the consensus state of a given client (at height `consensus_height`)
    /// matches the input `consensus_state`. The parameter `counterparty_height` represent the
    /// height of the counterparty chain that this proof assumes (i.e., the height at which this
    /// proof was computed).
    #[allow(clippy::too_many_arguments)]
    fn verify_client_consensus_state(
        &self,
        ctx: &dyn ReaderContext,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a connection state matches that of the input `connection_end`.
    #[allow(clippy::too_many_arguments)]
    fn verify_connection_state(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a channel state matches that of the input `channel_end`.
    #[allow(clippy::too_many_arguments)]
    fn verify_channel_state(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error>;

    /// Verify the client state for this chain that it is stored on the counterparty chain.
    #[allow(clippy::too_many_arguments)]
    fn verify_client_full_state(
        &self,
        ctx: &dyn ReaderContext,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        expected_client_state: &AnyClientState,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a packet has been commited.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_data(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        commitment: PacketCommitment,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a packet has been commited.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        ack: AcknowledgementCommitment,
    ) -> Result<(), Error>;

    /// Verify a `proof` that of the next_seq_received.
    #[allow(clippy::too_many_arguments)]
    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error>;

    /// Verify a `proof` that a packet has not been received.
    #[allow(clippy::too_many_arguments)]
    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug)]
pub enum AnyClient<HostFunctions: HostFunctionsProvider> {
    Tendermint(TendermintClient<HostFunctions>),
    #[cfg(any(test, feature = "ics11_beefy"))]
    Beefy(BeefyClient<HostFunctions>),
    #[cfg(any(test, feature = "ics11_beefy"))]
    Near(BeefyClient<HostFunctions>),
    #[cfg(any(test, feature = "mocks"))]
    Mock(MockClient),
}

impl<HostFunctions: HostFunctionsProvider> AnyClient<HostFunctions> {
    pub fn from_client_type(client_type: ClientType) -> Self {
        match client_type {
            ClientType::Tendermint => {
                Self::Tendermint(TendermintClient::<HostFunctions>::default())
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            ClientType::Beefy => Self::Beefy(BeefyClient::<HostFunctions>::default()),
            #[cfg(any(test, feature = "ics11_beefy"))]
            ClientType::Near => Self::Near(BeefyClient::<HostFunctions>::default()),
            #[cfg(any(test, feature = "mocks"))]
            ClientType::Mock => Self::Mock(MockClient::default()),
        }
    }
}

// ⚠️  Beware of the awful boilerplate below ⚠️
impl<HostFunctions: HostFunctionsProvider> ClientDef for AnyClient<HostFunctions> {
    type Header = AnyHeader;
    type ClientState = AnyClientState;
    type ConsensusState = AnyConsensusState;

    /// Validate an incoming header
    fn verify_header(
        &self,
        ctx: &dyn ReaderContext,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    header => AnyHeader::Tendermint,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_header(ctx, client_id, client_state, header)
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Beefy,
                    header => AnyHeader::Beefy,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_header(ctx, client_id, client_state, header)
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                // let (client_state, header) = downcast!(
                //     client_state => AnyClientState::Beefy,
                //     header => AnyHeader::Beefy,
                // )
                // .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                // client.verify_header(ctx, client_id, client_state, header)
                todo!()
            }

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Mock,
                    header => AnyHeader::Mock,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_header(ctx, client_id, client_state, header)
            }
        }
    }

    /// Validates an incoming `header` against the latest consensus state of this client.
    fn update_state(
        &self,
        ctx: &dyn ReaderContext,
        client_id: ClientId,
        client_state: AnyClientState,
        header: AnyHeader,
    ) -> Result<(AnyClientState, ConsensusUpdateResult), Error> {
        match self {
            Self::Tendermint(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    header => AnyHeader::Tendermint,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                let (new_state, new_consensus) =
                    client.update_state(ctx, client_id, client_state, header)?;

                Ok((AnyClientState::Tendermint(new_state), new_consensus))
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Beefy,
                    header => AnyHeader::Beefy,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                let (new_state, new_consensus) =
                    client.update_state(ctx, client_id, client_state, header)?;

                Ok((AnyClientState::Beefy(new_state), new_consensus))
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Mock,
                    header => AnyHeader::Mock,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                let (new_state, new_consensus) =
                    client.update_state(ctx, client_id, client_state, header)?;

                Ok((AnyClientState::Mock(new_state), new_consensus))
            }
        }
    }

    fn update_state_on_misbehaviour(
        &self,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<Self::ClientState, Error> {
        match self {
            AnyClient::Tendermint(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    header => AnyHeader::Tendermint,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;
                let client_state = client.update_state_on_misbehaviour(client_state, header)?;
                Ok(Self::ClientState::Tendermint(client_state))
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            AnyClient::Beefy(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Beefy,
                    header => AnyHeader::Beefy,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                let client_state = client.update_state_on_misbehaviour(client_state, header)?;
                Ok(Self::ClientState::Beefy(client_state))
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            AnyClient::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            AnyClient::Mock(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Mock,
                    header => AnyHeader::Mock,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                let client_state = client.update_state_on_misbehaviour(client_state, header)?;
                Ok(Self::ClientState::Mock(client_state))
            }
        }
    }

    /// Checks for misbehaviour in an incoming header
    fn check_for_misbehaviour(
        &self,
        ctx: &dyn ReaderContext,
        client_id: ClientId,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<bool, Error> {
        match self {
            AnyClient::Tendermint(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    header => AnyHeader::Tendermint,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;
                client.check_for_misbehaviour(ctx, client_id, client_state, header)
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            AnyClient::Beefy(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Beefy,
                    header => AnyHeader::Beefy,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.check_for_misbehaviour(ctx, client_id, client_state, header)
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            AnyClient::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            AnyClient::Mock(client) => {
                let (client_state, header) = downcast!(
                    client_state => AnyClientState::Mock,
                    header => AnyHeader::Mock,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.check_for_misbehaviour(ctx, client_id, client_state, header)
            }
        }
    }

    fn verify_upgrade_and_update_state(
        &self,
        client_state: &Self::ClientState,
        consensus_state: &Self::ConsensusState,
        proof_upgrade_client: Vec<u8>,
        proof_upgrade_consensus_state: Vec<u8>,
    ) -> Result<(Self::ClientState, ConsensusUpdateResult), Error> {
        match self {
            Self::Tendermint(client) => {
                let (client_state, consensus_state) = downcast!(
                    client_state => AnyClientState::Tendermint,
                    consensus_state => AnyConsensusState::Tendermint,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                let (new_state, new_consensus) = client.verify_upgrade_and_update_state(
                    client_state,
                    consensus_state,
                    proof_upgrade_client,
                    proof_upgrade_consensus_state,
                )?;

                Ok((AnyClientState::Tendermint(new_state), new_consensus))
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let (client_state, consensus_state) = downcast!(
                    client_state => AnyClientState::Beefy,
                    consensus_state => AnyConsensusState::Beefy,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                let (new_state, new_consensus) = client.verify_upgrade_and_update_state(
                    client_state,
                    consensus_state,
                    proof_upgrade_client,
                    proof_upgrade_consensus_state,
                )?;

                Ok((AnyClientState::Beefy(new_state), new_consensus))
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let (client_state, consensus_state) = downcast!(
                    client_state => AnyClientState::Mock,
                    consensus_state => AnyConsensusState::Mock,
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                let (new_state, new_consensus) = client.verify_upgrade_and_update_state(
                    client_state,
                    consensus_state,
                    proof_upgrade_client,
                    proof_upgrade_consensus_state,
                )?;

                Ok((AnyClientState::Mock(new_state), new_consensus))
            }
        }
    }

    fn verify_client_consensus_state(
        &self,
        ctx: &dyn ReaderContext,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        consensus_height: Height,
        expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_client_consensus_state(
                    ctx,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    client_id,
                    consensus_height,
                    expected_consensus_state,
                )
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Beefy
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_client_consensus_state(
                    ctx,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    client_id,
                    consensus_height,
                    expected_consensus_state,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_client_consensus_state(
                    ctx,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    client_id,
                    consensus_height,
                    expected_consensus_state,
                )
            }
        }
    }

    fn verify_connection_state(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &AnyClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        connection_id: &ConnectionId,
        expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(client_state => AnyClientState::Tendermint)
                    .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_connection_state(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    connection_id,
                    expected_connection_end,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(client_state => AnyClientState::Beefy)
                    .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_connection_state(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    connection_id,
                    expected_connection_end,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(client_state => AnyClientState::Mock)
                    .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_connection_state(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    connection_id,
                    expected_connection_end,
                )
            }
        }
    }

    fn verify_channel_state(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &AnyClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        expected_channel_end: &ChannelEnd,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(client_state => AnyClientState::Tendermint)
                    .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_channel_state(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    expected_channel_end,
                )
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(client_state => AnyClientState::Beefy)
                    .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_channel_state(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    expected_channel_end,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }

            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(client_state => AnyClientState::Mock)
                    .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_channel_state(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    expected_channel_end,
                )
            }
        }
    }
    fn verify_client_full_state(
        &self,
        ctx: &dyn ReaderContext,
        client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        client_id: &ClientId,
        client_state_on_counterparty: &AnyClientState,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_client_full_state(
                    ctx,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    client_id,
                    client_state_on_counterparty,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Beefy
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_client_full_state(
                    ctx,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    client_id,
                    client_state_on_counterparty,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_client_full_state(
                    ctx,
                    client_state,
                    height,
                    prefix,
                    proof,
                    root,
                    client_id,
                    client_state_on_counterparty,
                )
            }
        }
    }

    fn verify_packet_data(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        commitment: PacketCommitment,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_packet_data(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                    commitment,
                )
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Beefy
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_packet_data(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                    commitment,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_packet_data(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                    commitment,
                )
            }
        }
    }

    fn verify_packet_acknowledgement(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        ack_commitment: AcknowledgementCommitment,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_packet_acknowledgement(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                    ack_commitment,
                )
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Beefy
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_packet_acknowledgement(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                    ack_commitment,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_packet_acknowledgement(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                    ack_commitment,
                )
            }
        }
    }
    fn verify_next_sequence_recv(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_next_sequence_recv(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                )
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Beefy
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_next_sequence_recv(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_next_sequence_recv(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                )
            }
        }
    }

    fn verify_packet_receipt_absence(
        &self,
        ctx: &dyn ReaderContext,
        client_id: &ClientId,
        client_state: &Self::ClientState,
        height: Height,
        connection_end: &ConnectionEnd,
        proof: &CommitmentProofBytes,
        root: &CommitmentRoot,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
    ) -> Result<(), Error> {
        match self {
            Self::Tendermint(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Tendermint
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Tendermint))?;

                client.verify_packet_receipt_absence(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                )
            }

            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Beefy(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Beefy
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Beefy))?;

                client.verify_packet_receipt_absence(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                )
            }
            #[cfg(any(test, feature = "ics11_beefy"))]
            Self::Near(_) => {
                todo!()
            }
            #[cfg(any(test, feature = "mocks"))]
            Self::Mock(client) => {
                let client_state = downcast!(
                    client_state => AnyClientState::Mock
                )
                .ok_or_else(|| Error::client_args_type_mismatch(ClientType::Mock))?;

                client.verify_packet_receipt_absence(
                    ctx,
                    client_id,
                    client_state,
                    height,
                    connection_end,
                    proof,
                    root,
                    port_id,
                    channel_id,
                    sequence,
                )
            }
        }
    }
}

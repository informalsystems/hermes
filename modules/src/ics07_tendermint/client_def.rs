use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, ClientDef};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics07_tendermint::client_state::ClientState;
use crate::ics07_tendermint::consensus_state::ConsensusState;
use crate::ics07_tendermint::header::Header;
use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};
use crate::ics24_host::identifier::ClientId;
use crate::ics24_host::identifier::ConnectionId;
use tendermint::block::Height;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TendermintClient;

impl ClientDef for TendermintClient {
    type Header = Header;
    type ClientState = ClientState;
    type ConsensusState = ConsensusState;

    fn check_header_and_update_state(
        &self,
        _client_state: Self::ClientState,
        _header: Self::Header,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Box<dyn std::error::Error>> {
        todo!()
    }

    fn verify_client_consensus_state(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProof,
        _client_id: &ClientId,
        _consensus_height: Height,
        _expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }

    fn verify_connection_state(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _prefix: &CommitmentPrefix,
        _proof: &CommitmentProof,
        _connection_id: &ConnectionId,
        _expected_connection_end: &ConnectionEnd,
    ) -> Result<(), Box<dyn std::error::Error>> {
        todo!()
    }

    fn verify_client_full_state(
        &self,
        _client_state: &Self::ClientState,
        _height: Height,
        _root: &CommitmentRoot,
        _prefix: &CommitmentPrefix,
        _client_id: &ClientId,
        _proof: &CommitmentProof,
        _expected_client_state: &AnyClientState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        unimplemented!()
    }
}

use crate::ics23_commitment::{commitment::CommitmentPrefix, merkle::apply_prefix};
use crate::ics24_host::identifier::ConnectionId;
use crate::{ics02_client::client_def::ClientDef, ics24_host::identifier::ClientId};
use crate::{ics02_client::state::ClientState, ics23_commitment::commitment::CommitmentProof};
use crate::{ics03_connection::connection::ConnectionEnd, ics24_host::Path};

use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientState, MockConsensusState};

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics23_commitment::commitment::CommitmentRoot;
use tendermint::block::Height;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MockClient;

impl ClientDef for MockClient {
    type Header = MockHeader;
    type ClientState = MockClientState;
    type ConsensusState = MockConsensusState;

    fn check_header_and_update_state(
        &self,
        client_state: Self::ClientState,
        header: Self::Header,
    ) -> Result<(Self::ClientState, Self::ConsensusState), Box<dyn std::error::Error>> {
        if client_state.latest_height() >= header.height() {
            return Err("header height is lower than client latest".into());
        }

        Ok((MockClientState(header), MockConsensusState(header)))
    }

    fn verify_client_consensus_state(
        &self,
        _client_state: &Self::ClientState,
        height: Height,
        prefix: &CommitmentPrefix,
        _proof: &CommitmentProof,
        client_id: &ClientId,
        _consensus_height: Height,
        _expected_consensus_state: &AnyConsensusState,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let client_prefixed_path =
            Path::ConsensusState(client_id.clone(), height.value()).to_string();

        let _path = apply_prefix(prefix, client_prefixed_path)?;

        // TODO - add ctx to all client verification functions
        // let cs = ctx.fetch_self_consensus_state(height);
        // TODO - implement this
        // proof.verify_membership(cs.root(), path, expected_consensus_state)

        Ok(())
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
        Ok(())
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
        Ok(())
    }
}

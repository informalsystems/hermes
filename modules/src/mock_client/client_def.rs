use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, ClientDef};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProof, CommitmentRoot};
use crate::ics23_commitment::merkle::apply_prefix;
use crate::ics24_host::identifier::{ClientId, ConnectionId};
use crate::ics24_host::Path;
use crate::mock_client::header::MockHeader;
use crate::mock_client::state::{MockClientState, MockConsensusState};
use crate::Height;

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
            return Err(
                "received header height is lower than (or equal to) client latest height".into(),
            );
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
        let client_prefixed_path = Path::ClientConsensusState {
            client_id: client_id.clone(),
            epoch: height.version_number,
            height: height.version_height,
        }
        .to_string();

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

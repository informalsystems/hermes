use tendermint::{block::signed_header::SignedHeader, Hash};
use thiserror::Error;

use ibc::{
    ics07_tendermint::consensus_state::ConsensusState,
    ics23_commitment::commitment::CommitmentProof,
    ics24_host::identifier::{ChainId, ClientId},
    Height,
};

use crate::chain::handle::ChainHandle;
use crate::msgs::Datagram;

#[derive(Debug, Error)]
pub enum ForeignClientError {
    #[error("Fail")]
    Fail(),

    #[error("Verificaiton failed")]
    VerificationError(),

    #[error("Headers didn't match")]
    HeaderMismatch(),
}

pub struct ForeignClientConfig {
    client_id: ClientId,
    chain_id: ChainId,
}

impl ForeignClientConfig {
    pub fn new(client_id: ClientId, chain_id: ChainId) -> ForeignClientConfig {
        Self {
            client_id,
            chain_id,
        }
    }
}

pub struct ForeignClient {
    config: ForeignClientConfig,
}

impl ForeignClient {
    pub fn new(
        src_chain: &dyn ChainHandle,
        dst_chain: &dyn ChainHandle,
        config: ForeignClientConfig,
    ) -> Result<ForeignClient, ForeignClientError> {
        // TODO: Client Handshake
        Ok(ForeignClient { config })
    }

    // This is a completely different synchronous update strategy then bundeling a an update packet
    pub fn update(
        &mut self,
        src_chain: &dyn ChainHandle,
        dst_chain: &dyn ChainHandle,
        src_target_height: Height,
    ) -> Result<Height, ForeignClientError> {
        /*
        return Ok(src_target_height);
        let (src_consensus_state, dst_membership_proof) =
            dst_chain.consensus_state(src_chain.id(), src_target_height);

        let dst_sh = dst_chain.get_header(dst_membership_proof.height + 1);
        // type verifyMembership = (root: CommitmentRoot, proof: CommitmentProof, path: CommitmentPath, value: Value) => boolean (ICS-023)
        if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
            // Error: Destination chain provided invalid consensus_state
            return Err(ForeignClientError::VerificationError())
        }

        if src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
            return Err(ForeignClientError::HeaderMismatch())
        }

        while src_consensus_state.height < src_target_height {
            let src_signed_headers = src_chain.get_minimal_set(src_consensus_state.height, src_target_height);

            // if we actually want to do this we need to create a transaction
            // This might fail semantically due to competing relayers
            // Even if this fails, we need to continue
            // XXX FIXME
            dst_chain.submit(vec![create_client_update_datagram(src_signed_headers)]);

            let (src_consensus_state, dst_membership_proof) = dst_chain.consensus_state(src_chain.id(), src_target_height);
            let dst_sh = dst_chain.get_header(dst_membership_proof.height + 1);
            if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
                // Error: Destination chain provided invalid client_state
                return Err(ForeignClientError::VerificationError())
            }

            if src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
                // Error: consesus_state isn't verified by self light client
                return  Err(ForeignClientError::HeaderMismatch())
            }
        }
        */

        Ok(src_target_height)
    }
}

fn verify_consensus_state_inclusion(
    _consensus_state: &ConsensusState,
    _membership_proof: &CommitmentProof,
    _hash: &Hash,
) -> bool {
    true
}

// XXX: It's probably the link that can produce this
fn create_client_update_datagram(_header: Vec<SignedHeader>) -> Datagram {
    Datagram::NoOp()
}

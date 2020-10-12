use crate::types::{Height, Hash, ChainId, ClientId, SignedHeader, MembershipProof, ConsensusState};
use crate::msgs::Datagram;
use crate::chain::Chain;
use thiserror::Error;

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
    pub fn default() -> ForeignClientConfig {
        return ForeignClientConfig {
            client_id: "".to_string(),
            chain_id: 0,
        }
    }
}

pub struct ForeignClient {
    config: ForeignClientConfig,
}

impl ForeignClient {
    pub fn new(
        src_chain: &dyn Chain,
        dst_chain: &dyn Chain,
        config: ForeignClientConfig) -> Result<ForeignClient, ForeignClientError> {
        // TODO: Client Handshake
        return Ok(ForeignClient {
            config,
        })
    }

    // This is a completely different synchronous update strategy then bundeling a an update packet
    pub fn update(
        &mut self,
        src_chain: &dyn Chain,
        dst_chain: &dyn Chain,
        src_target_height: Height) -> Result<Height, ForeignClientError> {
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

        return Ok(src_target_height)
    }
}


fn verify_consensus_state_inclusion(_consensus_state: &ConsensusState, _membership_proof: &MembershipProof, _hash: &Hash) -> bool {
    return true
}

// XXX: It's probably the link that can produe this
fn create_client_update_datagram(_header: Vec<SignedHeader>) -> Datagram  {
    return Datagram::NoOp()
}


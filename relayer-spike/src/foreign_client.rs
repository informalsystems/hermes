use crate::types::{ChainId, ClientId, Datagram, Hash, Height};
use crate::chain::{Chain, SignedHeader, ConsensusState, MembershipProof};

pub enum ForeignClientError {
    VerificationError(),
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
    src_chain: Chain,
    dst_chain: Chain,
}

impl ForeignClient {
    pub fn new(
        src_chain: Chain,
        dst_chain: Chain,
        _config: ForeignClientConfig) -> Result<ForeignClient, ForeignClientError> {
        // TODO: Client Handshake
        return Ok(ForeignClient {
            src_chain,
            dst_chain,
        })
    }

    pub fn update(&mut self, src_target_height: Height) -> Result<Height, ForeignClientError> {
        let (mut src_consensus_state, mut dst_membership_proof) =
            self.dst_chain.consensus_state(self.src_chain.chain_id, src_target_height);

        let dst_sh = self.dst_chain.get_header(dst_membership_proof.height + 1);
        // type verifyMembership = (root: CommitmentRoot, proof: CommitmentProof, path: CommitmentPath, value: Value) => boolean (ICS-023)
        if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
            // Error: Destination chain provided invalid consensus_state
            return Err(ForeignClientError::VerificationError())
        }

        // verify client_state on self
        if self.src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
            return Err(ForeignClientError::HeaderMismatch())
        }

        while src_consensus_state.height < src_target_height {
            let src_signed_headers = self.src_chain.get_minimal_set(src_consensus_state.height, src_target_height);

            // This might fail semantically due to competing relayers
            // Even if this fails, we need to continue
            self.dst_chain.submit(vec![create_client_update_datagram(src_signed_headers)]);

            let (src_consensus_state, dst_membership_proof) = self.dst_chain.consensus_state(self.src_chain.chain_id, src_target_height);
            let dst_sh = self.dst_chain.get_header(dst_membership_proof.height + 1);
            if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
                // Error: Destination chain provided invalid client_state
                return Err(ForeignClientError::VerificationError())
            }

            if self.src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
                // Error: consesus_state isn't verified by self light client
                return  Err(ForeignClientError::HeaderMismatch())
            }
        }

        return Ok(src_target_height)
    }
}

fn verify_consensus_state_inclusion(_consensus_state: &ConsensusState, _membership_proof: &MembershipProof, _hash: &Hash) -> bool {
    return true
}

fn create_client_update_datagram(_header: Vec<SignedHeader>) -> Datagram  {
    return Datagram::NoOp()
}

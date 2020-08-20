use crate::types::*;

#[derive(std::cmp::PartialEq)]
pub struct Header {
    height: Height,
    hash: Hash,
    app_hash: Hash,
}


pub struct MembershipProof {
    height: Height,
}

impl Header {
    fn default() -> Header {
        return Header {
            height: 1,
            hash: (),
            app_hash: (),
        }
    }
}

pub type Subscription = Vec<Event>;

#[derive(Debug, Copy, Clone)]
pub struct FullNode {}

impl FullNode {
    pub fn subscribe(&self) -> Subscription {
        return vec![Event::NoOp()]
    }

    pub fn submit(&self, datagrams: Vec<Datagram>) {
    }

    pub fn consensus_state(&self, chain_id: ChainId, target_height: Height) -> (ConsensusState, MembershipProof) {
        // In practice this will query the client_state, get the height and perform a second query
        // for the consensus_state. it's possible that the client.state.height < target_height in which case this function will return the highest possible height

        return (ConsensusState::default(), MembershipProof{height: target_height})
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LightClient { }

impl LightClient {
    pub fn get_header(&self, height: Height) -> SignedHeader {
        return SignedHeader::default()
    }

    pub fn get_minimal_set(&self, from: Height, to: Height) -> Vec<SignedHeader> {
        return vec![SignedHeader::default()]
    }
}

pub enum ChainError {
    VerificationError(),
    HeaderMismatch(),
}


#[derive(Debug, Copy, Clone)]
pub struct Chain {
    chain_id: ChainId,
    pub full_node: FullNode,
    // requires rpc address for the full node
    pub light_client: LightClient,
    // queries require:
    // account_prefix
}


pub struct ConsensusState {
    height: Height, // Is this superflous?
    signed_header: SignedHeader,
}

impl ConsensusState {
    fn default() -> ConsensusState {
        return ConsensusState {
            height: 1,
            signed_header: SignedHeader::default(),
        }
    }
}
pub struct SignedHeader {
    header: Header,
    commit: (),
}

impl SignedHeader {
    fn default() -> SignedHeader {
        return SignedHeader {
            header:  Header::default(),
            commit: (),
        }
    }
}

pub enum Event {
    NoOp(),
}


impl Chain {
   pub fn new() -> Chain {
        return Chain { 
            chain_id: 0,
            full_node: FullNode {},
            light_client: LightClient {},
        }
    }

    // XXX: This will always return target_height_a or ClientError
    pub fn update_client(&mut self, dest: &Chain, self_target_height: Height) -> Result<Height, ChainError> {
        let (mut self_consensus_state, mut dest_membership_proof) = dest.full_node.consensus_state(self.chain_id, self_target_height);

        let dest_sh = dest.light_client.get_header(dest_membership_proof.height + 1);
        // type verifyMembership = (root: CommitmentRoot, proof: CommitmentProof, path: CommitmentPath, value: Value) => boolean (ICS-023)
        if ! verify_consensus_state_inclusion(&self_consensus_state, &dest_membership_proof, &(dest_sh.header.app_hash)) {
            // Error: Destination chain provided invalid consensus_state
            return Err(ChainError::VerificationError())
        }

        // verify client_state on self
        if self.light_client.get_header(self_consensus_state.height).header == self_consensus_state.signed_header.header {
            return Err(ChainError::HeaderMismatch())
        }

        while self_consensus_state.height < self_target_height {
            let self_signed_headers = self.light_client.get_minimal_set(self_consensus_state.height, self_target_height);

            // This might fail semantically due to competing relayers
            // Even if this fails, we need to continue
            dest.full_node.submit(vec![create_client_update_datagram(self_signed_headers)]);

            let (self_consensus_state, dest_membership_proof) = dest.full_node.consensus_state(self.chain_id, self_target_height);
            let dest_sh = dest.light_client.get_header(dest_membership_proof.height + 1);
            if ! verify_consensus_state_inclusion(&self_consensus_state, &dest_membership_proof, &(dest_sh.header.app_hash)) {
                // Error: Destination chain provided invalid client_state
                return Err(ChainError::VerificationError())
            }

            if self.light_client.get_header(self_consensus_state.height).header == self_consensus_state.signed_header.header {
                // Error: consesus_state isn't verified by self light client
                return  Err(ChainError::HeaderMismatch())
            }
        }

        return Ok(self_target_height)
    }
}

fn verify_consensus_state_inclusion(_consensus_state: &ConsensusState, _membership_proof: &MembershipProof, _hash: &Hash) -> bool {
    return true
}

fn create_client_update_datagram(_header: Vec<SignedHeader>) -> Datagram  {
    return Datagram::NoOp()
}

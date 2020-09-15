use crate::types::*;

#[derive(std::cmp::PartialEq)]
pub struct Header {
    pub height: Height,
    pub hash: Hash,
    pub app_hash: Hash,
}


pub struct MembershipProof {
    pub height: Height,
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
}

#[derive(Debug, Copy, Clone)]
pub struct Chain {
    pub chain_id: ChainId,
    pub full_node: FullNode,
    // requires rpc address for the full node
    pub light_client: LightClient,
    // queries require:
    // account_prefix
}


pub struct ConsensusState {
    pub height: Height, // Is this superflous?
    pub signed_header: SignedHeader,
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
    pub header: Header,
    pub commit: (),
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
    // Maybe return a chainError Here?
    pub fn new() -> Chain {
        return Chain { 
            chain_id: 0,
            full_node: FullNode {},
            light_client: LightClient {},
        }
    }

   pub fn run(self) -> Result<(), ChainError> {
       return Ok(())
   }
}


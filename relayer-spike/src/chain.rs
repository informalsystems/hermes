use crate::types::*;
use crossbeam_channel as channel;

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
pub enum ChainError {
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

#[derive(Debug, Copy, Clone)]
pub struct Chain {
    pub chain_id: ChainId,
    // TODO: account_prefix
}

// XXX: This should be a trait allowing a mock implementation
impl Chain {
    // Maybe return a ChainError Here?
    pub fn new() -> Chain {
        return Chain {
            chain_id: 0,
        }
    }

    // XXX: These methods will be proxies to the runtime
    pub fn get_header(&self, height: Height) -> SignedHeader {
        return SignedHeader::default()
    }

    pub fn get_minimal_set(&self, from: Height, to: Height) -> Vec<SignedHeader> {
        return vec![SignedHeader::default()]
    }

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

enum HandleInput {
    Terminate(channel::Sender<()>),
}

pub struct ChainRuntime {
    sender: channel::Sender<HandleInput>,
    receiver: channel::Receiver<HandleInput>,
}

impl ChainRuntime {
    // XXX: ChainConfig
    pub fn new() -> ChainRuntime {
        let (sender, receiver) = channel::unbounded::<HandleInput>();

        return Self {
            sender,
            receiver,
        }
    }

    pub fn handle(&self) -> Chain {
        return Chain::new();
    }

    pub fn run(mut self) -> Result<(), ChainError> {
        loop {
            let event = self.receiver.recv().unwrap();
            match event {
                HandleInput::Terminate(sender) => {
                    sender.send(()).unwrap();
                    return Ok(())
                }
            }
        }
    }
}


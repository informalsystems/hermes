use crate::types::*;
use crossbeam_channel as channel;
use std::time::Duration;

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

pub type Datagrams = Vec<Datagram>;
pub type Subscription = channel::Receiver<Datagrams>;

#[derive(Debug, Clone)]
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

pub trait Chain: Send {
    fn subscribe(&self, _chain_id: ChainId) -> Result<Subscription, ChainError>;

    // TODO: Error Handling
    fn get_header(&self, height: Height) -> SignedHeader;

    // TODO: Error handling
    fn get_minimal_set(&self, from: Height, to: Height) -> Vec<SignedHeader>;

    // TODO: Error handling
    fn submit(&self, datagrams: Vec<Datagram>);

    // TODO: Error handling
    fn consensus_state(&self, chain_id: ChainId, target_height: Height) -> (ConsensusState, MembershipProof);

    fn id(&self) -> ChainId;
}

#[derive(Debug, Clone)]
pub struct ProdChain {
    pub chain_id: ChainId,
    sender: channel::Sender<HandleInput>,
    // TODO: account_prefix
}

impl ProdChain {
    fn new(sender: channel::Sender<HandleInput>) -> Self {
        return Self {
            chain_id: 0,
            sender,
        }
    }

    // TODO: Figure this out
    // XXX: Move this to ChainRuntime
}

impl Chain for ProdChain {
    fn id(&self) -> ChainId {
        return self.chain_id
    }

    fn subscribe(&self, _chain_id: ChainId) -> Result<Subscription, ChainError> {
        let (sender, receiver) = channel::bounded::<Subscription>(1);
        self.sender.send(HandleInput::Subscribe(sender)).unwrap();
        return Ok(receiver.recv().unwrap());
    }

    fn get_header(&self, height: Height) -> SignedHeader {
        return SignedHeader::default()
    }

    fn get_minimal_set(&self, from: Height, to: Height) -> Vec<SignedHeader> {
        return vec![SignedHeader::default()]
    }

    fn submit(&self, datagrams: Vec<Datagram>) {
    }

    fn consensus_state(&self, chain_id: ChainId, target_height: Height) -> (ConsensusState, MembershipProof) {
        // In practice this will query the client_state, get the height and perform a second query
        // for the consensus_state. it's possible that the client.state.height < target_height in which case this function will return the highest possible height

        return (ConsensusState::default(), MembershipProof{height: target_height})
    }
}


enum HandleInput {
    Terminate(channel::Sender<()>),
    Subscribe(channel::Sender<Subscription>),
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

    pub fn handle(&self) -> ProdChain {
        let sender = self.sender.clone();
        return ProdChain::new(sender);
    }

    pub fn run(self) -> Result<(), ChainError> {
        // TODO: Replace with a websocket
        let event_monitor = channel::tick(Duration::from_millis(1000));

        let mut subscriptions: Vec<channel::Sender<Datagrams>> = vec![];
        loop {
            channel::select! {
                recv(event_monitor) -> tick => {
                    println!("tick tick!");
                    for subscription in subscriptions.iter() {
                        subscription.send(vec![Datagram::NoOp()]).unwrap();
                    }
                },
                recv(self.receiver) -> maybe_event => {
                    let event = maybe_event.unwrap();
                    match event {
                        HandleInput::Subscribe(sender) => {
                            println!("Subscribing!");
                            let (sub_sender, sub_receiver) = channel::unbounded::<Vec<Datagram>>();
                            subscriptions.push(sub_sender);
                            sender.send(sub_receiver).unwrap();
                        },
                        HandleInput::Terminate(sender) => {
                            sender.send(()).unwrap();
                            return Ok(())
                        }
                    }
                },
            }
        }
    }
}


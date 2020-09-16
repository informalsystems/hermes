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

pub type Subscription = Vec<Event>;

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

#[derive(Debug, Clone)]
pub enum Event {
    NoOp(),
}

#[derive(Debug, Clone)]
pub struct Chain {
    pub chain_id: ChainId,
    sender: channel::Sender<HandleInput>,
    // TODO: account_prefix
}

// XXX: This should be a trait allowing a mock implementation
impl Chain {
    // Maybe return a ChainError Here?
    fn new(sender: channel::Sender<HandleInput>) -> Chain {
        return Chain {
            chain_id: 0,
            sender,
        }
    }

    pub fn subscribe(&self, _chain_id: ChainId) -> channel::Receiver<Vec<Datagram>> {
        let (sender, receiver) = channel::bounded::<channel::Receiver<Vec<Datagram>>>(1);
        self.sender.send(HandleInput::Subscribe(sender)).unwrap();
        return receiver.recv().unwrap();
    }

    // XXX: These methods will be proxies to the runtime
    pub fn get_header(&self, height: Height) -> SignedHeader {
        return SignedHeader::default()
    }

    pub fn get_minimal_set(&self, from: Height, to: Height) -> Vec<SignedHeader> {
        return vec![SignedHeader::default()]
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
    Subscribe(channel::Sender<channel::Receiver<Vec<Datagram>>>),
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
        let sender = self.sender.clone();
        return Chain::new(sender);
    }
    // We need to:
    // * forward outgoing requests to external components (light_client, full_node)
    // * Read incomming events from the full_node
    //  * Relay Link specific messages to subscriptions
    pub fn run(mut self) -> Result<(), ChainError> {
        // XXX: Mock for now
        let event_monitor = channel::tick(Duration::from_millis(1000));

        let mut subscriptions: Vec<channel::Sender<Vec<Datagram>>> = vec![];
        loop {
            channel::select! {
                recv(event_monitor) -> tick => {
                    println!("tick tick!");
                    for subscription in subscriptions.iter() {
                        subscription.send(vec![Datagram::NoOp()]).unwrap();
                    }
                },
                recv(self.receiver) -> foo => {
                    let event = foo.unwrap();
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


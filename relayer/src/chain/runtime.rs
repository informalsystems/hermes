use crate::chain::handle::{cosmos::ProdChainHandle, ChainHandleError, HandleInput};
use crate::config::ChainConfig;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};

use ibc::ics24_host::identifier::ChainId;
use ibc::Height;

use crossbeam_channel as channel;
use std::time::Duration;

pub struct ChainRuntime {
    chain_id: ChainId,
    chain_config: ChainConfig,
    sender: channel::Sender<HandleInput>,
    receiver: channel::Receiver<HandleInput>,
}

impl ChainRuntime {
    pub fn new(chain_config: &ChainConfig) -> ChainRuntime {
        let (sender, receiver) = channel::unbounded::<HandleInput>();

        Self {
            chain_id: todo!(),
            chain_config: chain_config.clone(),
            sender,
            receiver,
        }
    }

    pub fn handle(&self) -> Result<ProdChainHandle, ChainHandleError> {
        let sender = self.sender.clone();
        ProdChainHandle::new(
            self.chain_id.clone(),
            sender,
            self.chain_config.rpc_addr.clone(),
        )
    }

    pub fn run(self) -> Result<(), ChainHandleError> {
        // Mocked: EventMonitor
        // What we need here is a reliable stream of events produced by a connected full node.
        // Events received from this stream will be buffered (perhaps durably) and then routed to
        // the various subscriptions.
        let event_monitor = channel::tick(Duration::from_millis(1000));

        let mut subscriptions: Vec<channel::Sender<(Height, Vec<IBCEvent>)>> = vec![];
        loop {
            channel::select! {
                recv(event_monitor) -> tick => {
                    println!("tick tick!");
                    for subscription in subscriptions.iter() {
                        let target_height = Height::new(0, 1); // FIXME
                        // subscription.send((target_height, vec![IBCEvent::NoOp()])).unwrap();
                    }
                },
                recv(self.receiver) -> maybe_event => {
                    let event = maybe_event.unwrap();
                    match event {
                        HandleInput::Subscribe(sender) => {
                            println!("Subscribing!");
                            let (sub_sender, sub_receiver) = channel::unbounded::<(Height, Vec<IBCEvent>)>();
                            subscriptions.push(sub_sender);
                            sender.send(sub_receiver).unwrap();
                        },
                        HandleInput::Terminate(sender) => {
                            sender.send(()).unwrap();
                        }
                    }
                },
            }
        }
    }
}

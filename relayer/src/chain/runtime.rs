use std::time::Duration;

use crossbeam_channel as channel;
use tendermint::block::signed_header::SignedHeader;
use thiserror::Error;

use ibc::{ics24_host::identifier::ChainId, Height};

use crate::config::ChainConfig;
use crate::foreign_client::ForeignClient;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};

use super::{
    error::ChainError,
    handle::{HandleInput, ProdChainHandle},
    Chain,
};

pub struct ChainRuntime<Chain> {
    chain: Chain,
    sender: channel::Sender<HandleInput>,
    receiver: channel::Receiver<HandleInput>,
}

impl<C: Chain> ChainRuntime<C> {
    pub fn from_config(config: ChainConfig) -> Result<ChainConfig, ChainError> {
        todo!()
    }

    pub fn new(chain: C) -> Self {
        let (sender, receiver) = channel::unbounded::<HandleInput>();

        Self {
            chain,
            sender,
            receiver,
        }
    }

    pub fn handle(&self) -> ProdChainHandle {
        let chain_id = self.chain.id().clone();
        let sender = self.sender.clone();

        ProdChainHandle::new(chain_id, sender)
    }

    pub fn run(self) -> Result<(), ChainError> {
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
                recv(self.receiver) -> event => {
                    match event {
                        Ok(HandleInput::Subscribe(sender)) => {
                            let (tx, rx) = channel::unbounded();
                            subscriptions.push(tx);
                            sender.send(rx).map_err(|e| ChainError::Channel)?;
                        },
                        Ok(HandleInput::Terminate(sender)) => {
                            sender.send(()).map_err(|e| ChainError::Channel)?;
                            break;
                        }
                        Ok(HandleInput::GetHeader(_height, _sender)) => {
                            todo!()
                        }
                        Err(e) => {
                            todo!()
                        }
                    }
                },
            }
        }

        Ok(())
    }
}

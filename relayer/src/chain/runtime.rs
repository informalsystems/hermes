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
    handle::{ChainHandle, HandleInput, ProdChainHandle},
    Chain, CosmosSDKChain,
};

pub struct ChainRuntime<Chain> {
    chain: Chain,
    sender: channel::Sender<HandleInput>,
    receiver: channel::Receiver<HandleInput>,
}

impl ChainRuntime<CosmosSDKChain> {
    pub fn cosmos_sdk(config: ChainConfig) -> Self {
        todo!()
    }
}

impl<C: Chain> ChainRuntime<C> {
    pub fn new(chain: C) -> Self {
        let (sender, receiver) = channel::unbounded::<HandleInput>();

        Self {
            chain,
            sender,
            receiver,
        }
    }

    pub fn handle(&self) -> impl ChainHandle {
        let chain_id = self.chain.id().clone();
        let sender = self.sender.clone();

        ProdChainHandle::new(chain_id, sender)
    }

    pub fn run(self) -> Result<(), ChainError> {
        loop {
            channel::select! {
                recv(self.receiver) -> event => {
                    match event {
                        Ok(HandleInput::Subscribe(sender)) => {
                            let (tx, rx) = channel::unbounded();
                            // TODO: Handle subscription
                            sender.send(Ok(rx)).map_err(|_| ChainError::Channel)?;
                        },
                        Ok(HandleInput::Terminate(sender)) => {
                            sender.send(Ok(())).map_err(|_| ChainError::Channel)?;
                            break;
                        }
                        Ok(HandleInput::GetHeader { height, reply_to }) => {
                            todo!()
                        }
                        Ok(HandleInput::GetMinimalSet {..}) => todo!(),
                        Ok(HandleInput::Query {..}) => todo!(),
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

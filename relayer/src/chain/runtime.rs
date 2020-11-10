use std::time::Duration;

use crossbeam_channel as channel;
use tendermint::block::signed_header::SignedHeader;
use thiserror::Error;

use ibc::{
    ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader},
    ics24_host::identifier::ChainId,
    ics24_host::Path,
    Height,
};

use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::foreign_client::ForeignClient;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};

use super::{
    handle::{ChainHandle, HandleInput, ProdChainHandle, ReplyTo, Subscription},
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

    pub fn run(self) -> Result<(), Error> {
        loop {
            channel::select! {
                recv(self.receiver) -> event => {
                    match event {
                        Ok(HandleInput::Terminate(reply_to)) => {
                            reply_to.send(Ok(())).map_err(|_| Kind::Channel)?;
                            break;
                        }
                        Ok(HandleInput::Subscribe(reply_to)) => {
                            self.subscribe(reply_to)?
                        },
                        Ok(HandleInput::Query {path, height, prove, reply_to}) => {
                            self.query(path, height, prove, reply_to)?
                        },
                        Ok(HandleInput::GetHeader { height, reply_to }) => {
                            self.get_header(height, reply_to)?
                        }
                        Ok(HandleInput::GetMinimalSet {..}) => todo!(),
                        Ok(HandleInput::Submit {..}) => todo!(),
                        Ok(HandleInput::GetHeight {..}) => todo!(),
                        Ok(HandleInput::CreatePacket {..}) => todo!(),
                        Ok(HandleInput::AssembleClientState {..}) => todo!(),
                        Ok(HandleInput::AssembleConsensusState {..}) => todo!(),
                        Err(e) => {
                            todo!()
                        }
                    }
                },
            }
        }

        Ok(())
    }

    fn subscribe(&self, reply_to: ReplyTo<Subscription>) -> Result<(), Error> {
        let (tx, rx) = channel::unbounded();
        // TODO: Handle subscription
        reply_to
            .send(Ok(rx))
            .map_err(|e| Kind::Channel.context(e))?;
        Ok(())
    }

    fn query(
        &self,
        path: Path,
        height: Height,
        prove: bool,
        reply_to: ReplyTo<Vec<u8>>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn get_header(&self, height: Height, reply_to: ReplyTo<AnyHeader>) -> Result<(), Error> {
        todo!()
    }

    fn get_minimal_set(
        from: Height,
        to: Height,
        reply_to: ReplyTo<Vec<AnyHeader>>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn submit(transaction: EncodedTransaction, reply_to: ReplyTo<()>) -> Result<(), Error> {
        todo!()
    }

    fn get_height(client: ForeignClient, reply_to: ReplyTo<Height>) -> Result<(), Error> {
        todo!()
    }

    fn create_packet(event: IBCEvent, reply_to: ReplyTo<Packet>) -> Result<(), Error> {
        todo!()
    }

    /// Given a header originating from this chain, constructs a client state.
    fn assemble_client_state(
        header: AnyHeader,
        reply_to: ReplyTo<AnyClientState>,
    ) -> Result<(), Error> {
        todo!()
    }

    /// Given a header originating from this chain, constructs a consensus state.
    fn assemble_consensus_state(
        header: AnyHeader,
        reply_to: ReplyTo<AnyConsensusState>,
    ) -> Result<(), Error> {
        todo!()
    }
}

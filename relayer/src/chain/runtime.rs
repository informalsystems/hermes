use std::time::Duration;

use crossbeam_channel as channel;
use tendermint::block::signed_header::SignedHeader;
use thiserror::Error;

use ibc::{
    ics02_client::{
        client_def::{AnyClientState, AnyConsensusState, AnyHeader},
        state::{ClientState, ConsensusState},
    },
    ics24_host::identifier::ChainId,
    ics24_host::Path,
    Height,
};

use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};
use crate::{config::ChainConfig, util::block_on};
use crate::{
    error::{Error, Kind},
    light_client::{tendermint::LightClient as TMLightClient, LightClient},
};
use crate::{foreign_client::ForeignClient, light_client::LightBlock};

use super::{
    handle::{ChainHandle, HandleInput, ProdChainHandle, ReplyTo, Subscription},
    Chain, CosmosSDKChain,
};

pub struct ChainRuntime<C: Chain> {
    chain: C,
    sender: channel::Sender<HandleInput>,
    receiver: channel::Receiver<HandleInput>,
    light_client: Box<dyn LightClient<C>>,
}

impl ChainRuntime<CosmosSDKChain> {
    pub fn cosmos_sdk(config: ChainConfig, light_client: TMLightClient) -> Result<Self, Error> {
        let chain = CosmosSDKChain::from_config(config)?;
        Ok(Self::new(chain, light_client))
    }
}

impl<C: Chain> ChainRuntime<C> {
    pub fn new(chain: C, light_client: impl LightClient<C> + 'static) -> Self {
        let (sender, receiver) = channel::unbounded::<HandleInput>();

        Self {
            chain,
            sender,
            receiver,
            light_client: Box::new(light_client),
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
                        Ok(HandleInput::Query { path, height, prove, reply_to, }) => {
                            self.query(path, height, prove, reply_to)?
                        },
                        Ok(HandleInput::GetHeader { height, reply_to }) => {
                            self.get_header(height, reply_to)?
                        }
                        Ok(HandleInput::GetMinimalSet { from, to, reply_to }) => {
                            self.get_minimal_set(from, to, reply_to)?
                        }
                        Ok(HandleInput::Submit { transaction, reply_to, }) => {
                            self.submit(transaction, reply_to)?
                        },
                        Ok(HandleInput::GetHeight { client, reply_to }) => {
                            self.get_height(client, reply_to)?
                        }
                        Ok(HandleInput::CreatePacket { event, reply_to }) => {
                            self.create_packet(event, reply_to)?
                        }
                        Ok(HandleInput::AssembleClientState { header, reply_to }) => {
                            self.assemble_client_state(header, reply_to)?
                        }
                        Ok(HandleInput::AssembleConsensusState { header, reply_to }) => {
                            self.assemble_consensus_state(header, reply_to)?
                        }
                        Err(e) => todo!(),
                    }
                },
            }
        }

        Ok(())
    }

    fn subscribe(&self, reply_to: ReplyTo<Subscription>) -> Result<(), Error> {
        todo!()
    }

    fn query(
        &self,
        path: Path,
        height: Height,
        prove: bool,
        reply_to: ReplyTo<Vec<u8>>,
    ) -> Result<(), Error> {
        if !path.is_provable() & prove {
            reply_to
                .send(Err(Kind::NonProvableData.into()))
                .map_err(|e| Kind::Channel.context(e))?;
            return Ok(());
        }

        let response = self.chain.query(path, height, prove);

        // Verify response proof, if requested.
        if prove {
            dbg!("TODO: implement proof verification."); // TODO: Verify proof
        }

        reply_to
            .send(response)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn get_header(&self, height: Height, reply_to: ReplyTo<AnyHeader>) -> Result<(), Error> {
        let light_block = self.light_client.verify_to_target(height);
        let header: Result<AnyHeader, _> = todo!(); // light_block.map(|lb| lb.signed_header().wrap_any());

        reply_to
            .send(header)
            .map_err(|e| Kind::Channel.context(e))?;

        Ok(())
    }

    fn get_minimal_set(
        &self,
        from: Height,
        to: Height,
        reply_to: ReplyTo<Vec<AnyHeader>>,
    ) -> Result<(), Error> {
        todo!()
    }

    fn submit(&self, transaction: EncodedTransaction, reply_to: ReplyTo<()>) -> Result<(), Error> {
        todo!()
    }

    fn get_height(&self, client: ForeignClient, reply_to: ReplyTo<Height>) -> Result<(), Error> {
        todo!()
    }

    fn create_packet(&self, event: IBCEvent, reply_to: ReplyTo<Packet>) -> Result<(), Error> {
        todo!()
    }

    /// Given a header originating from this chain, constructs a client state.
    fn assemble_client_state(
        &self,
        header: AnyHeader,
        reply_to: ReplyTo<AnyClientState>,
    ) -> Result<(), Error> {
        if let Some(header) = self.chain.downcast_header(header) {
            let client_state = self
                .chain
                .assemble_client_state(&header)
                .map(|cs| cs.wrap_any());

            reply_to
                .send(client_state)
                .map_err(|e| Kind::Channel.context(e))?;

            Ok(())
        } else {
            Err(Kind::InvalidInputHeader.into())
        }
    }

    /// Given a header originating from this chain, constructs a consensus state.
    fn assemble_consensus_state(
        &self,
        header: AnyHeader,
        reply_to: ReplyTo<AnyConsensusState>,
    ) -> Result<(), Error> {
        if let Some(header) = self.chain.downcast_header(header) {
            let consensus_state = self
                .chain
                .assemble_consensus_state(&header)
                .map(|cs| cs.wrap_any());

            reply_to
                .send(consensus_state)
                .map_err(|e| Kind::Channel.context(e))?;

            Ok(())
        } else {
            Err(Kind::InvalidInputHeader.into())
        }
    }
}

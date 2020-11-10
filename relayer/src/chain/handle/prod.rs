use crossbeam_channel as channel;

use ibc::{
    events::IBCEvent, ics02_client::client_def::AnyHeader, ics24_host::identifier::ChainId, Height,
};
use tendermint_light_client::types::SignedHeader;

use crate::{
    error::{Error, Kind},
    foreign_client::ForeignClient,
    msgs::{EncodedTransaction, Packet},
};

use super::{reply_channel, ChainHandle, HandleInput, ReplyTo, Subscription};

#[derive(Debug, Clone)]
pub struct ProdChainHandle {
    chain_id: ChainId,
    sender: channel::Sender<HandleInput>,
}

impl ProdChainHandle {
    pub fn new(chain_id: ChainId, sender: channel::Sender<HandleInput>) -> Self {
        Self { chain_id, sender }
    }
}

impl ChainHandle for ProdChainHandle {
    fn id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn subscribe(&self, _chain_id: ChainId) -> Result<Subscription, Error> {
        let (sender, receiver) = reply_channel();

        self.sender
            .send(HandleInput::Subscribe(sender))
            .map_err(|e| Kind::Channel)?;

        receiver.recv().map_err(|e| Kind::Channel)?
    }

    fn get_header(&self, height: Height) -> Result<AnyHeader, Error> {
        let (sender, receiver) = reply_channel();

        self.sender
            .send(HandleInput::GetHeader {
                height,
                reply_to: sender,
            })
            .map_err(|e| Kind::Channel)?;

        receiver.recv().map_err(|e| Kind::Channel)?
    }

    fn query(
        &self,
        path: ibc::ics24_host::Path,
        height: Height,
        prove: bool,
    ) -> Result<Vec<u8>, Error> {
        todo!()
    }

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, Error> {
        todo!()
    }

    fn submit(&self, transaction: EncodedTransaction) -> Result<(), Error> {
        todo!()
    }

    fn get_height(&self, client: &ForeignClient) -> Result<Height, Error> {
        todo!()
    }

    fn create_packet(&self, event: IBCEvent) -> Result<Packet, Error> {
        todo!()
    }

    fn assemble_client_state(
        &self,
        header: &AnyHeader,
    ) -> Result<ibc::ics02_client::client_def::AnyClientState, Error> {
        todo!()
    }

    fn assemble_consensus_state(
        &self,
        header: &AnyHeader,
    ) -> Result<ibc::ics02_client::client_def::AnyConsensusState, Error> {
        todo!()
    }
}

use crossbeam_channel as channel;

use ibc::{
    events::IBCEvent, ics02_client::client_def::AnyHeader, ics24_host::identifier::ChainId, Height,
};
use tendermint_light_client::types::SignedHeader;

use crate::{
    chain::{error::ChainError, Subscription},
    foreign_client::ForeignClient,
    msgs::{EncodedTransaction, Packet},
};

use super::{ChainHandle, HandleInput};

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

    fn subscribe(&self, _chain_id: ChainId) -> Result<Subscription, ChainError> {
        let (sender, receiver) = channel::bounded::<Subscription>(1);

        self.sender
            .send(HandleInput::Subscribe(sender))
            .map_err(|e| ChainError::Channel)?;

        Ok(receiver.recv().map_err(|e| ChainError::Channel)?)
    }

    fn get_header(&self, height: Height) -> Result<AnyHeader, ChainError> {
        let (sender, receiver) = channel::bounded::<AnyHeader>(1);

        self.sender
            .send(HandleInput::GetHeader(height, sender))
            .map_err(|e| ChainError::Channel)?;

        Ok(receiver.recv().map_err(|e| ChainError::Channel)?)
    }

    fn query(
        &self,
        path: ibc::ics24_host::Path,
        height: Height,
        prove: bool,
    ) -> Result<Vec<u8>, ChainError> {
        todo!()
    }

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, ChainError> {
        todo!()
    }

    fn submit(&self, transaction: EncodedTransaction) -> Result<(), ChainError> {
        todo!()
    }

    fn get_height(&self, client: &ForeignClient) -> Result<Height, ChainError> {
        todo!()
    }

    fn create_packet(&self, event: IBCEvent) -> Result<Packet, ChainError> {
        todo!()
    }

    fn assemble_client_state(
        &self,
        header: &AnyHeader,
    ) -> Result<ibc::ics02_client::client_def::AnyClientState, ChainError> {
        todo!()
    }

    fn assemble_consensus_state(
        &self,
        header: &AnyHeader,
    ) -> Result<ibc::ics02_client::client_def::AnyConsensusState, ChainError> {
        todo!()
    }
}

use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::one_for_all::components::batch::BatchComponents;
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::error::Error;
use crate::cosmos::message::CosmosIbcMessage;
use crate::cosmos::traits::chain::{CosmosChain, CosmosChainWithBatch};

#[derive(Clone)]
pub struct CosmosChainImpl<Handle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub batch_sender: mpsc::Sender<(
        Vec<CosmosIbcMessage>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )>,
}

impl<Handle> CosmosChainImpl<Handle> {
    pub fn new(
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        key_entry: KeyEntry,
    ) -> (
        Self,
        mpsc::Receiver<(
            Vec<CosmosIbcMessage>,
            oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
        )>,
    ) {
        let (batch_sender, receiver) = mpsc::channel(1024);

        let chain = Self {
            handle,
            signer,
            tx_config,
            key_entry,
            batch_sender,
        };

        (chain, receiver)
    }
}

impl<Handle> CosmosChain for CosmosChainImpl<Handle>
where
    Handle: ChainHandle,
{
    type Components = BatchComponents;

    type ChainHandle = Handle;

    fn chain_handle(&self) -> &Self::ChainHandle {
        &self.handle
    }

    fn signer(&self) -> &Signer {
        &self.signer
    }

    fn tx_config(&self) -> &TxConfig {
        &self.tx_config
    }

    fn key_entry(&self) -> &KeyEntry {
        &self.key_entry
    }
}

impl<Handle> CosmosChainWithBatch for CosmosChainImpl<Handle>
where
    Handle: ChainHandle,
{
    fn batch_sender(
        &self,
    ) -> &mpsc::Sender<(
        Vec<CosmosIbcMessage>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )> {
        &self.batch_sender
    }
}

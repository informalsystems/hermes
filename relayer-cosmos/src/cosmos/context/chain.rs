use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::one_for_all::components::batch::BatchComponents;
use ibc_relayer_framework::one_for_all::impls::message::OfaMessage;
use std::sync::{Arc, Mutex};
use tendermint::abci::responses::Event;
use tokio::sync::{mpsc, oneshot};

use crate::cosmos::error::Error;
use crate::cosmos::traits::chain::{CosmosChain, CosmosChainWithBatch};
use crate::cosmos::types::chain::CosmosChainContext;

#[derive(Clone)]
pub struct CosmosChainImpl<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub batch_sender: mpsc::Sender<(
        Vec<OfaMessage<CosmosChainContext<Self>>>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )>,
    pub batch_receiver: Arc<
        Mutex<
            mpsc::Receiver<(
                Vec<OfaMessage<CosmosChainContext<Self>>>,
                oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
            )>,
        >,
    >,
}

impl<Handle: ChainHandle> CosmosChainImpl<Handle> {
    pub fn new(handle: Handle, signer: Signer, tx_config: TxConfig, key_entry: KeyEntry) -> Self {
        let (batch_sender, receiver) = mpsc::channel(1024);

        let chain = Self {
            handle,
            signer,
            tx_config,
            key_entry,
            batch_sender,
            batch_receiver: Arc::new(Mutex::new(receiver)),
        };

        chain
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
        Vec<OfaMessage<CosmosChainContext<Self>>>,
        oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
    )> {
        &self.batch_sender
    }

    fn batch_receiver(
        &self,
    ) -> &Mutex<
        mpsc::Receiver<(
            Vec<OfaMessage<CosmosChainContext<Self>>>,
            oneshot::Sender<Result<Vec<Vec<Event>>, Error>>,
        )>,
    > {
        &self.batch_receiver
    }
}

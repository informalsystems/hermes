use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::one_for_all::components::batch::BatchComponents;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;

use crate::cosmos::core::traits::batch::CosmosChainWithBatch;
use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::types::batch::{BatchReceiver, BatchSender};

#[derive(Clone)]
pub struct CosmosChainEnv<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub batch_sender: BatchSender<Self>,
    pub batch_receiver: BatchReceiver<Self>,
}

impl<Handle: ChainHandle> CosmosChainEnv<Handle> {
    pub fn new(handle: Handle, signer: Signer, tx_config: TxConfig, key_entry: KeyEntry) -> Self {
        let (batch_sender, receiver) = mpsc::unbounded_channel();

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

impl<Handle> CosmosChain for CosmosChainEnv<Handle>
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

impl<Handle> CosmosChainWithBatch for CosmosChainEnv<Handle>
where
    Handle: ChainHandle,
{
    fn batch_sender(&self) -> &BatchSender<Self> {
        &self.batch_sender
    }

    fn batch_receiver(&self) -> &BatchReceiver<Self> {
        &self.batch_receiver
    }
}

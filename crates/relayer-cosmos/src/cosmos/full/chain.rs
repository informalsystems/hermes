use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::base::one_for_all::traits::batch::OfaBatchContext;
use ibc_relayer_framework::full::batch::context::new_batch_channel;
use ibc_relayer_framework::full::one_for_all::components::full::FullComponents;
use ibc_relayer_types::signer::Signer;

use crate::cosmos::core::traits::batch::CosmosChainWithBatch;
use crate::cosmos::core::traits::chain::CosmosChain;
use crate::cosmos::core::types::batch::CosmosBatchChannel;
use crate::cosmos::core::types::chain::CosmosChainContext;

#[derive(Clone)]
pub struct CosmosChainEnv<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub batch_channel: CosmosBatchChannel,
}

impl<Handle: ChainHandle> CosmosChainEnv<Handle> {
    pub fn new(handle: Handle, signer: Signer, tx_config: TxConfig, key_entry: KeyEntry) -> Self {
        let batch_channel = new_batch_channel::<OfaBatchContext<CosmosChainContext<Self>>>();

        let chain = Self {
            handle,
            signer,
            tx_config,
            key_entry,
            batch_channel,
        };

        chain
    }
}

impl<Handle> CosmosChain for CosmosChainEnv<Handle>
where
    Handle: ChainHandle,
{
    type Components = FullComponents;

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
    fn batch_channel(&self) -> &CosmosBatchChannel {
        &self.batch_channel
    }
}

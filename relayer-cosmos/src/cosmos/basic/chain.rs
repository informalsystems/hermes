use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::one_for_all::components::default::DefaultComponents;

use crate::cosmos::core::traits::chain::CosmosChain;

#[derive(Clone)]
pub struct CosmosChainEnv<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
}

impl<Handle: ChainHandle> CosmosChainEnv<Handle> {
    pub fn new(handle: Handle, signer: Signer, tx_config: TxConfig, key_entry: KeyEntry) -> Self {
        Self {
            handle,
            signer,
            tx_config,
            key_entry,
        }
    }
}

impl<Handle> CosmosChain for CosmosChainEnv<Handle>
where
    Handle: ChainHandle,
{
    type Components = DefaultComponents;

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

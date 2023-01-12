use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_framework::base::one_for_all::presets::min::MinimalPreset;
use ibc_relayer_types::signer::Signer;

use crate::base::traits::chain::CosmosChain;

pub struct MinCosmosChainContext<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub websocket_url: String,
    pub key_entry: Secp256k1KeyPair,
}

impl<Handle: ChainHandle> MinCosmosChainContext<Handle> {
    pub fn new(
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        websocket_url: String,
        key_entry: Secp256k1KeyPair,
    ) -> Self {
        Self {
            handle,
            signer,
            tx_config,
            websocket_url,
            key_entry,
        }
    }
}

impl<Handle> CosmosChain for MinCosmosChainContext<Handle>
where
    Handle: ChainHandle,
{
    type Preset = MinimalPreset;

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

    fn websocket_url(&self) -> &str {
        &self.websocket_url
    }

    fn key_entry(&self) -> &Secp256k1KeyPair {
        &self.key_entry
    }
}

use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_all_in_one::base::one_for_all::presets::min::MinimalPreset;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::signer::Signer;
use tendermint_rpc::{HttpClient, Url};

use crate::base::traits::chain::CosmosChain;

pub struct MinCosmosChainContext<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub rpc_client: HttpClient,
    pub websocket_url: Url,
    pub key_entry: Secp256k1KeyPair,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
}

impl<Handle: ChainHandle> MinCosmosChainContext<Handle> {
    pub fn new(
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        rpc_client: HttpClient,
        websocket_url: Url,
        key_entry: Secp256k1KeyPair,
        runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    ) -> Self {
        Self {
            handle,
            signer,
            tx_config,
            rpc_client,
            websocket_url,
            key_entry,
            runtime,
        }
    }
}

impl<Handle> CosmosChain for MinCosmosChainContext<Handle>
where
    Handle: ChainHandle,
{
    type Preset = MinimalPreset;

    type ChainHandle = Handle;

    fn runtime(&self) -> &OfaRuntimeWrapper<TokioRuntimeContext> {
        &self.runtime
    }

    fn chain_handle(&self) -> &Self::ChainHandle {
        &self.handle
    }

    fn signer(&self) -> &Signer {
        &self.signer
    }

    fn tx_config(&self) -> &TxConfig {
        &self.tx_config
    }

    fn rpc_client(&self) -> &HttpClient {
        &self.rpc_client
    }

    fn websocket_url(&self) -> &Url {
        &self.websocket_url
    }

    fn key_entry(&self) -> &Secp256k1KeyPair {
        &self.key_entry
    }
}

use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;

use crate::tokio::context::TokioRuntimeContext;

#[derive(Clone)]
pub struct CosmosChainContext<Handle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub runtime: OfaRuntimeContext<TokioRuntimeContext>,
}

impl<Handle> CosmosChainContext<Handle> {
    pub fn new(
        runtime: TokioRuntimeContext,
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        key_entry: KeyEntry,
    ) -> Self {
        let runtime = OfaRuntimeContext::new(runtime);

        Self {
            handle,
            signer,
            tx_config,
            key_entry,
            runtime,
        }
    }
}

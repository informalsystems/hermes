use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_framework::full::one_for_all::presets::full::FullPreset;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;
use ibc_relayer_types::signer::Signer;

use crate::base::traits::chain::CosmosChain;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::types::telemetry::CosmosTelemetry;

#[derive(Clone)]
pub struct FullCosmosChainContext<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: Secp256k1KeyPair,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
}

impl<Handle: ChainHandle> FullCosmosChainContext<Handle> {
    pub fn new(
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        key_entry: Secp256k1KeyPair,
        telemetry: CosmosTelemetry,
    ) -> Self {
        let chain = Self {
            handle,
            signer,
            tx_config,
            key_entry,
            telemetry: OfaTelemetryWrapper::new(telemetry),
        };

        chain
    }
}

impl<Handle> CosmosChain for FullCosmosChainContext<Handle>
where
    Handle: ChainHandle,
{
    type Preset = FullPreset;

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

    fn key_entry(&self) -> &Secp256k1KeyPair {
        &self.key_entry
    }
}

impl<Handle> CosmosFullChain for FullCosmosChainContext<Handle>
where
    Handle: ChainHandle,
{
    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry> {
        &self.telemetry
    }
}

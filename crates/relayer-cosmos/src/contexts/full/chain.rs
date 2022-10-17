use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::full::batch::context::new_batch_channel;
use ibc_relayer_framework::full::one_for_all::components::full::FullPreset;
use ibc_relayer_framework::full::one_for_all::traits::batch::OfaBatchContext;
use ibc_relayer_framework::full::one_for_all::traits::telemetry::OfaTelemetryWrapper;
use ibc_relayer_types::signer::Signer;

use crate::base::traits::chain::CosmosChain;
use crate::base::types::chain::CosmosChainWrapper;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::types::batch::CosmosBatchChannel;
use crate::full::types::telemetry::CosmosTelemetry;

#[derive(Clone)]
pub struct CosmosChainContext<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub batch_channel: CosmosBatchChannel,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
}

impl<Handle: ChainHandle> CosmosChainContext<Handle> {
    pub fn new(
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        key_entry: KeyEntry,
        telemetry: CosmosTelemetry,
    ) -> Self {
        let batch_channel = new_batch_channel::<OfaBatchContext<CosmosChainWrapper<Self>>>();

        let chain = Self {
            handle,
            signer,
            tx_config,
            key_entry,
            batch_channel,
            telemetry: OfaTelemetryWrapper::new(telemetry),
        };

        chain
    }
}

impl<Handle> CosmosChain for CosmosChainContext<Handle>
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

    fn key_entry(&self) -> &KeyEntry {
        &self.key_entry
    }
}

impl<Handle> CosmosFullChain for CosmosChainContext<Handle>
where
    Handle: ChainHandle,
{
    fn batch_channel(&self) -> &CosmosBatchChannel {
        &self.batch_channel
    }

    fn telemetry(&self) -> &OfaTelemetryWrapper<CosmosTelemetry> {
        &self.telemetry
    }
}

use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::EventSourceMode;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_all_in_one::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::extra::one_for_all::presets::full::FullPreset;
use ibc_relayer_all_in_one::extra::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::signer::Signer;
use tendermint_rpc::client::CompatMode;
use tendermint_rpc::HttpClient;

use crate::base::traits::chain::CosmosChain;
use crate::full::traits::chain::CosmosFullChain;
use crate::full::types::telemetry::CosmosTelemetry;

#[derive(Clone)]
pub struct FullCosmosChainContext<Handle: ChainHandle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub rpc_client: HttpClient,
    pub compat_mode: CompatMode,
    pub key_entry: Secp256k1KeyPair,
    pub event_source_mode: EventSourceMode,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
}

impl<Handle: ChainHandle> FullCosmosChainContext<Handle> {
    pub fn new(
        handle: Handle,
        signer: Signer,
        tx_config: TxConfig,
        rpc_client: HttpClient,
        compat_mode: CompatMode,
        key_entry: Secp256k1KeyPair,
        event_source_mode: EventSourceMode,
        runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
        telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    ) -> Self {
        let chain = Self {
            handle,
            signer,
            tx_config,
            rpc_client,
            compat_mode,
            key_entry,
            event_source_mode,
            runtime,
            telemetry,
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

    fn compat_mode(&self) -> &CompatMode {
        &self.compat_mode
    }

    fn key_entry(&self) -> &Secp256k1KeyPair {
        &self.key_entry
    }

    fn event_source_mode(&self) -> &EventSourceMode {
        &self.event_source_mode
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

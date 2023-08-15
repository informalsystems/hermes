use alloc::sync::Arc;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::EventSourceMode;
use ibc_relayer::event::source::queries::all as all_queries;
use ibc_relayer::keyring::Secp256k1KeyPair;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_all_in_one::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_all_in_one::one_for_all::types::transaction::OfaTxWrapper;
use ibc_relayer_components::runtime::impls::subscription::empty::EmptySubscription;
use ibc_relayer_components::runtime::traits::subscription::Subscription;
use ibc_relayer_runtime::types::runtime::TokioRuntimeContext;
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use tendermint::abci::Event as AbciEvent;
use tendermint_rpc::client::CompatMode;
use tendermint_rpc::HttpClient;

use crate::contexts::transaction::CosmosTxContext;
use crate::impls::subscription::CanCreateAbciEventSubscription;
use crate::types::telemetry::CosmosTelemetry;

#[derive(Clone)]
pub struct CosmosChain<Handle: ChainHandle> {
    pub handle: Handle,
    pub chain_id: ChainId,
    pub compat_mode: CompatMode,
    pub runtime: TokioRuntimeContext,
    pub telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    pub subscription: Arc<dyn Subscription<Item = (Height, Arc<AbciEvent>)>>,
    pub tx_context: OfaTxWrapper<CosmosTxContext>,
}

impl<Handle: ChainHandle> CosmosChain<Handle> {
    pub fn new(
        handle: Handle,
        tx_config: TxConfig,
        rpc_client: HttpClient,
        compat_mode: CompatMode,
        key_entry: Secp256k1KeyPair,
        event_source_mode: EventSourceMode,
        runtime: TokioRuntimeContext,
        telemetry: OfaTelemetryWrapper<CosmosTelemetry>,
    ) -> Self {
        let chain_version = tx_config.chain_id.version();

        let subscription = match event_source_mode {
            EventSourceMode::Push {
                url,
                batch_delay: _,
            } => {
                runtime.new_abci_event_subscription(chain_version, url, compat_mode, all_queries())
            }
            EventSourceMode::Pull { interval: _ } => {
                // TODO: implement pull-based event source
                Arc::new(EmptySubscription::new())
            }
        };

        let chain_id = tx_config.chain_id.clone();

        let tx_context = OfaTxWrapper::new(CosmosTxContext::new(
            tx_config,
            rpc_client,
            key_entry,
            runtime.clone(),
        ));

        let chain = Self {
            handle,
            chain_id,
            compat_mode,
            runtime,
            telemetry,
            subscription,
            tx_context,
        };

        chain
    }
}

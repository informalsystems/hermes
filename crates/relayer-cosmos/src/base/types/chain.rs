use alloc::sync::Arc;
use ibc_relayer::event::monitor::queries::all;
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::base::one_for_all::types::transaction::OfaTxWrapper;
use ibc_relayer_framework::base::runtime::traits::subscription::Subscription;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics02_client::height::Height;
use tendermint::abci::Event as AbciEvent;

use crate::base::impls::subscription::CanCreateAbciEventSubscription;
use crate::base::traits::chain::CosmosChain;
use crate::base::types::transaction::CosmosTxWrapper;

pub struct CosmosChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub tx_context: OfaTxWrapper<CosmosTxWrapper<Chain>>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
    pub subscription: Arc<dyn Subscription<Item = (Height, AbciEvent)>>,
}

impl<Chain> CosmosChainWrapper<Chain>
where
    Chain: CosmosChain,
{
    pub fn new(chain: Arc<Chain>, runtime: OfaRuntimeWrapper<TokioRuntimeContext>) -> Self {
        let chain_version = chain.tx_config().chain_id.version();
        let subscription = runtime.new_abci_event_subscription(
            chain_version,
            chain.websocket_url().clone(),
            all(),
        );

        let tx_context = OfaTxWrapper::new(CosmosTxWrapper::new(chain.clone(), runtime.clone()));

        Self {
            chain,
            runtime,
            tx_context,
            subscription,
        }
    }
}

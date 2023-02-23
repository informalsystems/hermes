use alloc::sync::Arc;

use ibc_relayer::event::monitor::queries::all;
use ibc_relayer_all_in_one::base::one_for_all::types::transaction::OfaTxWrapper;
use ibc_relayer_components::runtime::traits::subscription::Subscription;
use ibc_relayer_types::core::ics02_client::height::Height;
use tendermint::abci::Event as AbciEvent;

use crate::base::impls::subscription::CanCreateAbciEventSubscription;
use crate::base::traits::chain::CosmosChain;
use crate::base::types::transaction::CosmosTxWrapper;

pub struct CosmosChainWrapper<Chain> {
    pub chain: Arc<Chain>,
    pub tx_context: OfaTxWrapper<CosmosTxWrapper<Chain>>,
    pub subscription: Arc<dyn Subscription<Item = (Height, AbciEvent)>>,
}

impl<Chain> CosmosChainWrapper<Chain>
where
    Chain: CosmosChain,
{
    pub fn new(chain: Arc<Chain>) -> Self {
        let chain_version = chain.tx_config().chain_id.version();
        let subscription = chain.runtime().new_abci_event_subscription(
            chain_version,
            chain.websocket_url().clone(),
            all(),
        );

        let tx_context = OfaTxWrapper::new(CosmosTxWrapper::new(chain.clone()));

        Self {
            chain,
            tx_context,
            subscription,
        }
    }
}

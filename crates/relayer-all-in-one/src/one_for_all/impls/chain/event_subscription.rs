use alloc::sync::Arc;

use crate::one_for_all::traits::chain::OfaBaseChain;
use crate::one_for_all::types::chain::OfaChainWrapper;
use ibc_relayer_components::chain::traits::event_subscription::HasEventSubscription;
use ibc_relayer_components::runtime::traits::subscription::Subscription;

impl<Chain> HasEventSubscription for OfaChainWrapper<Chain>
where
    Chain: OfaBaseChain,
{
    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Self::Height, Self::Event)>> {
        self.chain.event_subscription()
    }
}

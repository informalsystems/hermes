use async_trait::async_trait;

use crate::base::chain::traits::types::event::HasEventSource;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait EventRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventSource,
{
    async fn relay_chain_events(
        relayer: &Relay,
        event_source: &<Target::TargetChain as HasEventSource>::EventSource,
    ) -> Result<(), Relay::Error>;
}

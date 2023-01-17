use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait AutoRelayer<Relay>: Async
where
    Relay: HasRelayTypes,
{
    async fn auto_relay(relay: &Relay) -> Result<(), Relay::Error>;
}

#[async_trait]
pub trait AutoRelayerWithTarget<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn auto_relay_with_target(relay: &Relay) -> Result<(), Relay::Error>;
}

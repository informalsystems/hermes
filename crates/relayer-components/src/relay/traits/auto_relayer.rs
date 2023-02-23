use async_trait::async_trait;

use crate::core::traits::sync::Async;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanAutoRelay: Async {
    async fn auto_relay(&self);
}

#[async_trait]
pub trait AutoRelayer<Relay>: Async
where
    Relay: Async,
{
    async fn auto_relay(relay: &Relay);
}

#[async_trait]
pub trait AutoRelayerWithTarget<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn auto_relay_with_target(relay: &Relay);
}

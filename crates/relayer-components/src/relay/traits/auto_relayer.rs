use async_trait::async_trait;

use crate::core::traits::error::HasErrorType;
use crate::core::traits::sync::Async;
use crate::relay::traits::target::ChainTarget;
use crate::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanAutoRelay: HasErrorType {
    async fn auto_relay(&self) -> Result<(), Self::Error>;
}

#[async_trait]
pub trait AutoRelayer<Context>: Async
where
    Context: HasErrorType,
{
    async fn auto_relay(context: &Context) -> Result<(), Context::Error>;
}

#[async_trait]
pub trait AutoRelayerWithTarget<Relay, Target>: Async
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn auto_relay_with_target(relay: &Relay) -> Result<(), Relay::Error>;
}

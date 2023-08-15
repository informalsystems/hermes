use async_trait::async_trait;

use crate::core::traits::component::DelegateComponent;
use crate::core::traits::error::HasErrorType;
use crate::core::traits::sync::Async;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct AutoRelayerComponent;

/// Provider trait for the `CanAutoRelay` trait.
#[async_trait]
pub trait AutoRelayer<Relay>: Async
where
    Relay: HasErrorType,
{
    /// Starts the auto-relaying process for the given `Relay`.
    async fn auto_relay(relay: &Relay) -> Result<(), Relay::Error>;
}

#[async_trait]
impl<Relay, Component> AutoRelayer<Relay> for Component
where
    Relay: HasErrorType,
    Component: DelegateComponent<AutoRelayerComponent>,
    Component::Delegate: AutoRelayer<Relay>,
{
    async fn auto_relay(relay: &Relay) -> Result<(), Relay::Error> {
        Component::Delegate::auto_relay(relay).await
    }
}

/// Trait that encodes the capability of a relayer to relay
/// in a "set it and forget it" manner. This trait is agnostic
/// as far as the provided context is concerned, i.e., it doesn't
/// require an implementing type to be of any particular context.
///
/// For example, if this trait is implemented for a two-way relay
/// context, then starting the auto-relay process will handle relaying
/// between both connected chains in a bi-directional manner. If it is
/// instead implemented for a one-way relay context, then starting the
/// auto-relay process will relay in one direction as appropriate for
/// the implementing context.
#[async_trait]
pub trait CanAutoRelay: HasErrorType {
    /// Starts the auto-relaying process.
    async fn auto_relay(&self) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay> CanAutoRelay for Relay
where
    Relay: HasErrorType + DelegateComponent<AutoRelayerComponent>,
    Relay::Delegate: AutoRelayer<Relay>,
{
    async fn auto_relay(&self) -> Result<(), Self::Error> {
        Relay::Delegate::auto_relay(self).await
    }
}

/// Similar to the `CanAutoRelay` trait, the main differences are that this
/// trait only relays to a specific target, i.e., in one direction, as well
/// as the fact that it is specific to the `Relay` context.
#[async_trait]
pub trait AutoRelayerWithTarget<Relay, Target>: Async
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    /// Starts the auto-relaying process of relaying to the given `Relay` context's
    /// target.
    async fn auto_relay_with_target(relay: &Relay) -> Result<(), Relay::Error>;
}

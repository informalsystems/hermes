use async_trait::async_trait;

use crate::chain::traits::types::event::HasEventType;
use crate::chain::types::aliases::{Event, Height};
use crate::core::traits::component::{DelegateComponent, HasComponents};
use crate::core::traits::sync::Async;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct EventRelayerComponent;

/**
   An event relayer performs relay actions based on one event at a time from
   the target chain.

   The event relayer is a general abstraction over other relayer types that
   need to be reactive to chain events. This includes the
   [packet relayer]( crate::relay::traits::components::packet_relayer::CanRelayPacket),
   but also future relayers such as connection and channel handshake relayers.
*/
#[async_trait]
pub trait EventRelayer<Relay, Target>: Async
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventType,
{
    /**
       Relay a chain event which is emitted from the target chain at a given
       height.

       The chain event could be anything. If the given event is not related to
       IBC, the relayer should do nothing and return `Ok(())`.
    */
    async fn relay_chain_event(
        relay: &Relay,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Relay::Error>;
}

#[async_trait]
impl<Relay, Target, Component> EventRelayer<Relay, Target> for Component
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventType,
    Component: DelegateComponent<EventRelayerComponent>,
    Component::Delegate: EventRelayer<Relay, Target>,
{
    async fn relay_chain_event(
        relay: &Relay,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Relay::Error> {
        Component::Delegate::relay_chain_event(relay, height, event).await
    }
}

#[async_trait]
pub trait CanRelayEvent<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
    Target::TargetChain: HasEventType,
{
    async fn relay_chain_event(
        &self,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay, Target> CanRelayEvent<Target> for Relay
where
    Relay: HasRelayChains + HasComponents,
    Target: ChainTarget<Relay>,
    Target::TargetChain: HasEventType,
    Relay::Components: EventRelayer<Relay, Target>,
{
    async fn relay_chain_event(
        &self,
        height: &Height<Target::TargetChain>,
        event: &Event<Target::TargetChain>,
    ) -> Result<(), Self::Error> {
        Relay::Components::relay_chain_event(self, height, event).await
    }
}

use async_trait::async_trait;

use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::types::aliases::{Event, Height};
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

/**
   An event relayer performs relay actions based on one event at a time from
   the target chain.

   The event relayer is a general abstraction over other relayer types that
   need to be reactive to chain events. This includes the
   [packet relayer]( crate::base::relay::traits::packet_relayer::CanRelayPacket),
   but also future relayers such as connection and channel handshake relayers.
*/
#[async_trait]
pub trait EventRelayer<Relay, Target>: Async
where
    Relay: HasRelayTypes,
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
pub trait CanRelayEvent<Target>: HasRelayTypes
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

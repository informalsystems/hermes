use crate::chain::traits::event_subscription::HasEventSubscription;
use crate::components::default::closures::relay::event_relayer::UseDefaultEventRelayer;
use crate::components::default::relay::DefaultRelayComponents;
use crate::core::traits::component::HasComponents;
use crate::core::traits::sync::Async;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::components::auto_relayer::CanAutoRelay;

pub trait CanUseDefaultAutoRelayer: UseDefaultAutoRelayer {}

pub trait UseDefaultAutoRelayer: CanAutoRelay {}

impl<Relay, BaseRelayComponents> UseDefaultAutoRelayer for Relay
where
    Relay: HasRelayChains
        + UseDefaultEventRelayer
        + HasComponents<Components = DefaultRelayComponents<BaseRelayComponents>>,
    Relay::SrcChain: HasEventSubscription,
    Relay::DstChain: HasEventSubscription,
    BaseRelayComponents: Async,
{
}

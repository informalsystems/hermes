use ibc_relayer_components::chain::traits::event_subscription::HasEventSubscription;
use ibc_relayer_components::chain::traits::logs::event::CanLogChainEvent;
use ibc_relayer_components::chain::traits::types::chain_id::HasChainId;
use ibc_relayer_components::core::traits::component::HasComponents;
use ibc_relayer_components::core::traits::sync::Async;
use ibc_relayer_components::logger::traits::has_logger::{HasLogger, HasLoggerType};
use ibc_relayer_components::logger::traits::level::HasBaseLogLevels;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::components::auto_relayer::CanAutoRelay;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::components::extra::closures::relay::event_relayer::UseExtraEventRelayer;
use crate::components::extra::relay::ExtraRelayComponents;
use crate::runtime::traits::spawn::HasSpawner;

pub trait CanUseExtraAutoRelayer: UseExtraAutoRelayer {}

pub trait UseExtraAutoRelayer: CanAutoRelay {}

impl<Relay, BaseRelayComponents> UseExtraAutoRelayer for Relay
where
    Relay: Clone
        + HasRuntime
        + HasLogger
        + HasRelayChains
        + UseExtraEventRelayer
        + HasComponents<Components = ExtraRelayComponents<BaseRelayComponents>>,
    Relay::SrcChain: HasRuntime
        + HasChainId
        + HasEventSubscription
        + HasLoggerType<Logger = Relay::Logger>
        + CanLogChainEvent,
    Relay::DstChain: HasRuntime
        + HasChainId
        + HasEventSubscription
        + HasLoggerType<Logger = Relay::Logger>
        + CanLogChainEvent,
    Relay::Runtime: HasSpawner,
    Relay::Logger: HasBaseLogLevels,
    <Relay::SrcChain as HasRuntime>::Runtime: HasSpawner,
    <Relay::DstChain as HasRuntime>::Runtime: HasSpawner,
    BaseRelayComponents: Async,
{
}

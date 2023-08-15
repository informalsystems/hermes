use async_trait::async_trait;

use crate::chain::types::aliases::{Height, Message};
use crate::core::traits::component::DelegateComponent;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct UpdateClientMessageBuilderComponent;

#[async_trait]
pub trait UpdateClientMessageBuilder<Relay, Target>
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
{
    async fn build_update_client_messages(
        relay: &Relay,
        _target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Relay::Error>;
}

#[async_trait]
impl<Relay, Target, Component> UpdateClientMessageBuilder<Relay, Target> for Component
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
    Component: DelegateComponent<UpdateClientMessageBuilderComponent>,
    Component::Delegate: UpdateClientMessageBuilder<Relay, Target>,
{
    async fn build_update_client_messages(
        relay: &Relay,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Relay::Error> {
        Component::Delegate::build_update_client_messages(relay, target, height).await
    }
}

#[async_trait]
pub trait CanBuildUpdateClientMessage<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    async fn build_update_client_messages(
        &self,
        _target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Self::Error>;
}

#[async_trait]
impl<Relay, Target> CanBuildUpdateClientMessage<Target> for Relay
where
    Relay: HasRelayChains + DelegateComponent<UpdateClientMessageBuilderComponent>,
    Target: ChainTarget<Relay>,
    Relay::Delegate: UpdateClientMessageBuilder<Relay, Target>,
{
    async fn build_update_client_messages(
        &self,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Self::Error> {
        Relay::Delegate::build_update_client_messages(self, target, height).await
    }
}

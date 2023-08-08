use async_trait::async_trait;

use crate::chain::types::aliases::{Height, Message};
use crate::core::traits::component::HasComponents;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

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
    Relay: HasRelayChains + HasComponents,
    Target: ChainTarget<Relay>,
    Relay::Components: UpdateClientMessageBuilder<Relay, Target>,
{
    async fn build_update_client_messages(
        &self,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Self::Error> {
        Relay::Components::build_update_client_messages(self, target, height).await
    }
}

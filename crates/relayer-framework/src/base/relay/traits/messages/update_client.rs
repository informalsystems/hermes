use async_trait::async_trait;

use crate::base::chain::types::aliases::{Height, Message};
use crate::base::relay::traits::context::HasRelayTypes;
use crate::base::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

#[async_trait]
pub trait HasUpdateClientMessageBuilder<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
{
    type UpdateClientMessageBuilder: UpdateClientMessageBuilder<Self, Target>;

    async fn build_update_client_messages(
        &self,
        _target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Self::Error> {
        Self::UpdateClientMessageBuilder::build_update_client_messages(self, height).await
    }
}

#[async_trait]
pub trait UpdateClientMessageBuilder<Relay, Target>
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay>,
{
    async fn build_update_client_messages(
        context: &Relay,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Relay::Error>;
}

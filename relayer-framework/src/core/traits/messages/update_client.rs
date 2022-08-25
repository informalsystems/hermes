use async_trait::async_trait;

use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::target::ChainTarget;
use crate::core::types::aliases::{Height, IbcMessage};
use crate::std_prelude::*;

#[async_trait]
pub trait HasUpdateClientMessageBuilder<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    type UpdateClientMessageBuilder: UpdateClientMessageBuilder<Self, Target>;

    async fn build_update_client_messages(
        &self,
        _target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>, Self::Error> {
        Self::UpdateClientMessageBuilder::build_update_client_messages(self, height).await
    }
}

#[async_trait]
pub trait UpdateClientMessageBuilder<Relay, Target>
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    async fn build_update_client_messages(
        context: &Relay,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>, Relay::Error>;
}

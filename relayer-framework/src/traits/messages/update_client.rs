use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::contexts::relay::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
pub trait CanUpdateClient<Target>: RelayContext
where
    Target: ChainTarget<Self>,
{
    type UpdateClientMessageBuilder: UpdateClientMessageBuilder<Self, Target>;

    async fn build_update_client_messages(
        &self,
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

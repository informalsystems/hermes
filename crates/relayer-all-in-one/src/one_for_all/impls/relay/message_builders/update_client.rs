use async_trait::async_trait;
use ibc_relayer_components::chain::types::aliases::{Height, Message};
use ibc_relayer_components::relay::traits::messages::update_client::{
    CanBuildUpdateClientMessage, UpdateClientMessageBuilder,
};
use ibc_relayer_components::relay::traits::target::ChainTarget;

use crate::one_for_all::components;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Target> CanBuildUpdateClientMessage<Target> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
    Target: ChainTarget<Self>,
    components::UpdateClientMessageBuilder: UpdateClientMessageBuilder<Self, Target>,
{
    async fn build_update_client_messages(
        &self,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Self::Error> {
        components::UpdateClientMessageBuilder::build_update_client_messages(self, target, height)
            .await
    }
}

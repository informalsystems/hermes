use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::OfaBaseChainTypes;
use crate::base::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::ibc_message_sender::{CanSendIbcMessages, IbcMessageSender};
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Components> CanSendIbcMessages<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    async fn send_messages(
        &self,
        messages: Vec<<Relay::SrcChain as OfaBaseChainTypes>::Message>,
    ) -> Result<Vec<Vec<<Relay::SrcChain as OfaBaseChainTypes>::Event>>, Self::Error> {
        <Components::IbcMessageSender as IbcMessageSender<Self, SourceTarget>>::send_messages(
            self, messages,
        )
        .await
    }
}

#[async_trait]
impl<Relay, Components> CanSendIbcMessages<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    async fn send_messages(
        &self,
        messages: Vec<<Relay::DstChain as OfaBaseChainTypes>::Message>,
    ) -> Result<Vec<Vec<<Relay::DstChain as OfaBaseChainTypes>::Event>>, Self::Error> {
        <Components::IbcMessageSender as IbcMessageSender<Self, DestinationTarget>>::send_messages(
            self, messages,
        )
        .await
    }
}

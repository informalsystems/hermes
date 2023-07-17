use async_trait::async_trait;
use ibc_relayer_components::relay::traits::ibc_message_sender::{
    CanSendIbcMessages, IbcMessageSender,
};
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};

use crate::one_for_all::components;
use crate::one_for_all::traits::chain::OfaChainTypes;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay> CanSendIbcMessages<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn send_messages(
        &self,
        _target: SourceTarget,
        messages: Vec<<Relay::SrcChain as OfaChainTypes>::Message>,
    ) -> Result<Vec<Vec<<Relay::SrcChain as OfaChainTypes>::Event>>, Self::Error> {
        <components::IbcMessageSender as IbcMessageSender<Self, SourceTarget>>::send_messages(
            self, messages,
        )
        .await
    }
}

#[async_trait]
impl<Relay> CanSendIbcMessages<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn send_messages(
        &self,
        _target: DestinationTarget,
        messages: Vec<<Relay::DstChain as OfaChainTypes>::Message>,
    ) -> Result<Vec<Vec<<Relay::DstChain as OfaChainTypes>::Event>>, Self::Error> {
        <components::IbcMessageSender as IbcMessageSender<Self, DestinationTarget>>::send_messages(
            self, messages,
        )
        .await
    }
}

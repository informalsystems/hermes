use async_trait::async_trait;
use ibc_relayer_components::relay::traits::ibc_message_sender::{
    CanSendIbcMessages, IbcMessageSender,
};
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::traits::relay::OfaRelayPreset;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

#[async_trait]
impl<Relay, Preset> CanSendIbcMessages<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn send_messages(
        &self,
        messages: Vec<<Relay::SrcChain as OfaChainTypes>::Message>,
    ) -> Result<Vec<Vec<<Relay::SrcChain as OfaChainTypes>::Event>>, Self::Error> {
        <Preset::IbcMessageSender as IbcMessageSender<Self, SourceTarget>>::send_messages(
            self, messages,
        )
        .await
    }
}

#[async_trait]
impl<Relay, Preset> CanSendIbcMessages<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaRelayPreset<Relay>,
{
    async fn send_messages(
        &self,
        messages: Vec<<Relay::DstChain as OfaChainTypes>::Message>,
    ) -> Result<Vec<Vec<<Relay::DstChain as OfaChainTypes>::Event>>, Self::Error> {
        <Preset::IbcMessageSender as IbcMessageSender<Self, DestinationTarget>>::send_messages(
            self, messages,
        )
        .await
    }
}

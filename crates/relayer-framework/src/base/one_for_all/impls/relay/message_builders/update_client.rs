use async_trait::async_trait;

use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaChainTypes};
use crate::base::one_for_all::traits::components::relay::OfaRelayComponents;
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::messages::update_client::{
    CanBuildUpdateClientMessage, UpdateClientMessageBuilder,
};
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::std_prelude::*;

pub struct BuildUpdateClientMessageFromOfa;

#[async_trait]
impl<Relay, SrcChain> UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, SourceTarget>
    for BuildUpdateClientMessageFromOfa
where
    Relay: OfaBaseRelay<SrcChain = SrcChain>,
    SrcChain: OfaBaseChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        _target: SourceTarget,
        height: &<Relay::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<SrcChain::Message>, Relay::Error> {
        let messages = context
            .relay
            .build_src_update_client_messages(height)
            .await?;

        Ok(messages)
    }
}

#[async_trait]
impl<Relay, DstChain> UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, DestinationTarget>
    for BuildUpdateClientMessageFromOfa
where
    Relay: OfaBaseRelay<DstChain = DstChain>,
    DstChain: OfaBaseChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        _target: DestinationTarget,
        height: &<Relay::SrcChain as OfaChainTypes>::Height,
    ) -> Result<Vec<DstChain::Message>, Relay::Error> {
        let messages = context
            .relay
            .build_dst_update_client_messages(height)
            .await?;

        Ok(messages)
    }
}

#[async_trait]
impl<Relay, Components> CanBuildUpdateClientMessage<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    async fn build_update_client_messages(
        &self,
        target: SourceTarget,
        height: &<Relay::DstChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Relay::SrcChain as OfaChainTypes>::Message>, Self::Error> {
        Components::UpdateClientMessageBuilder::build_update_client_messages(self, target, height)
            .await
    }
}

#[async_trait]
impl<Relay, Components> CanBuildUpdateClientMessage<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaRelayComponents<Relay>,
{
    async fn build_update_client_messages(
        &self,
        target: DestinationTarget,
        height: &<Relay::SrcChain as OfaChainTypes>::Height,
    ) -> Result<Vec<<Relay::DstChain as OfaChainTypes>::Message>, Self::Error> {
        Components::UpdateClientMessageBuilder::build_update_client_messages(self, target, height)
            .await
    }
}

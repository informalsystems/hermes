use async_trait::async_trait;
use ibc_relayer_components::chain::types::aliases::{Height, Message};
use ibc_relayer_components::relay::traits::messages::update_client::{
    CanBuildUpdateClientMessage, UpdateClientMessageBuilder,
};
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::relay::traits::target::{DestinationTarget, SourceTarget};

use crate::one_for_all::components;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::traits::relay::OfaRelay;
use crate::one_for_all::types::relay::OfaRelayWrapper;
use crate::std_prelude::*;

pub struct BuildUpdateClientMessageFromOfa;

#[async_trait]
impl<Relay, SrcChain> UpdateClientMessageBuilder<OfaRelayWrapper<Relay>, SourceTarget>
    for BuildUpdateClientMessageFromOfa
where
    Relay: OfaRelay<SrcChain = SrcChain>,
    SrcChain: OfaChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        _target: SourceTarget,
        height: &<Relay::DstChain as OfaChain>::Height,
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
    Relay: OfaRelay<DstChain = DstChain>,
    DstChain: OfaChain,
{
    async fn build_update_client_messages(
        context: &OfaRelayWrapper<Relay>,
        _target: DestinationTarget,
        height: &<Relay::SrcChain as OfaChain>::Height,
    ) -> Result<Vec<DstChain::Message>, Relay::Error> {
        let messages = context
            .relay
            .build_dst_update_client_messages(height)
            .await?;

        Ok(messages)
    }
}

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

use async_trait::async_trait;

use crate::base::chain::types::aliases::{Height, Message};
use crate::base::one_for_all::traits::chain::{OfaBaseChain, OfaChainTypes};
use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::impls::messages::skip_update_client::SkipUpdateClient;
use crate::base::relay::impls::messages::wait_update_client::WaitUpdateClient;
use crate::base::relay::traits::messages::update_client::{
    CanBuildUpdateClientMessage, UpdateClientMessageBuilder,
};
use crate::base::relay::traits::target::{ChainTarget, DestinationTarget, SourceTarget};
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
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
impl<Relay, Target> CanBuildUpdateClientMessage<Target> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay,
    Target: ChainTarget<Self>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessageFromOfa>>:
        UpdateClientMessageBuilder<Self, Target>,
{
    async fn build_update_client_messages(
        &self,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Self::Error> {
        <SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessageFromOfa>>>::build_update_client_messages(self, target, height).await
    }
}

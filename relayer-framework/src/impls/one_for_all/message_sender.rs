use async_trait::async_trait;

use crate::impls::one_for_all::chain::OfaChainContext;
use crate::impls::one_for_all::error::OfaErrorContext;
use crate::impls::one_for_all::message::OfaMessage;
use crate::impls::one_for_all::relay::OfaRelayContext;
use crate::std_prelude::*;
use crate::traits::ibc_message_sender::{IbcMessageSender, IbcMessageSenderContext};
use crate::traits::message_sender::{MessageSender, MessageSenderContext};
use crate::traits::one_for_all::chain::OfaChain;
use crate::traits::one_for_all::relay::OfaRelay;
use crate::traits::target::{DestinationTarget, SourceTarget};

pub struct OfaMessageSender;

impl<Chain: OfaChain> MessageSenderContext for OfaChainContext<Chain> {
    type MessageSender = OfaMessageSender;
}

impl<Relay: OfaRelay> IbcMessageSenderContext<SourceTarget> for OfaRelayContext<Relay> {
    type IbcMessageSender = OfaMessageSender;
}

impl<Relay: OfaRelay> IbcMessageSenderContext<DestinationTarget> for OfaRelayContext<Relay> {
    type IbcMessageSender = OfaMessageSender;
}

#[async_trait]
impl<Chain: OfaChain> MessageSender<OfaChainContext<Chain>> for OfaMessageSender {
    async fn send_messages(
        context: &OfaChainContext<Chain>,
        messages: Vec<OfaMessage<Chain>>,
    ) -> Result<Vec<Vec<Chain::Event>>, OfaErrorContext<Chain::Error>> {
        let in_messages = messages.into_iter().map(|m| m.message).collect();

        let events = context.chain.send_messages(in_messages).await?;

        Ok(events)
    }
}

#[async_trait]
impl<Relay: OfaRelay> IbcMessageSender<OfaRelayContext<Relay>, SourceTarget> for OfaMessageSender {
    async fn send_messages(
        context: &OfaRelayContext<Relay>,
        messages: Vec<OfaMessage<Relay::SrcChain>>,
    ) -> Result<Vec<Vec<<Relay::SrcChain as OfaChain>::Event>>, OfaErrorContext<Relay::Error>> {
        let in_messages = messages.into_iter().map(|m| m.message).collect();

        let events = context.src_chain.chain.send_messages(in_messages).await?;

        Ok(events)
    }
}

#[async_trait]
impl<Relay: OfaRelay> IbcMessageSender<OfaRelayContext<Relay>, DestinationTarget>
    for OfaMessageSender
{
    async fn send_messages(
        context: &OfaRelayContext<Relay>,
        messages: Vec<OfaMessage<Relay::DstChain>>,
    ) -> Result<Vec<Vec<<Relay::DstChain as OfaChain>::Event>>, OfaErrorContext<Relay::Error>> {
        let in_messages = messages.into_iter().map(|m| m.message).collect();

        let events = context.dst_chain.chain.send_messages(in_messages).await?;

        Ok(events)
    }
}

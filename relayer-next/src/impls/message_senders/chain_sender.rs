use async_trait::async_trait;

use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message_sender::{MessageSender, MessageSenderContext};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;

pub struct SendIbcMessageToChain;

#[async_trait]
impl<Context, Target, Message, Event> IbcMessageSender<Context, Target> for SendIbcMessageToChain
where
    Message: Async,
    Event: Async,
    Context: RelayContext,
    Target: ChainTarget<Context>,
    Target::TargetChain: MessageSenderContext,
    Target::TargetChain: IbcChainContext<
        Target::CounterpartyChain,
        Message = Message,
        IbcMessage = Message,
        Event = Event,
        IbcEvent = Event,
    >,
{
    async fn send_messages(
        &self,
        context: &Context,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        let target_chain = Target::target_chain(context);

        let events = target_chain
            .message_sender()
            .send_messages(target_chain, messages)
            .await?;

        Ok(events)
    }
}

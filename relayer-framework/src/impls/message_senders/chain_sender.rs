use async_trait::async_trait;

use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message_sender::{MessageSender, MessageSenderContext};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;

pub struct SendIbcMessagesToChain;

#[async_trait]
impl<Context, Target, TargetChain, Message, Event, Error> IbcMessageSender<Context, Target>
    for SendIbcMessagesToChain
where
    Message: Async,
    Event: Async,
    Context: RelayContext<Error = Error>,
    Target: ChainTarget<Context, TargetChain = TargetChain>,
    TargetChain: MessageSenderContext,
    TargetChain: IbcChainContext<
        Target::CounterpartyChain,
        Message = Message,
        IbcMessage = Message,
        Event = Event,
        IbcEvent = Event,
        Error = Error,
    >,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Error> {
        let events =
            TargetChain::MessageSender::send_messages(Target::target_chain(context), messages)
                .await?;

        Ok(events)
    }
}

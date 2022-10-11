use async_trait::async_trait;

use crate::base::core::traits::sync::Async;
use crate::base::traits::contexts::chain::IbcChainContext;
use crate::base::traits::contexts::relay::RelayContext;
use crate::base::traits::ibc_message_sender::IbcMessageSender;
use crate::base::traits::message_sender::{HasMessageSender, MessageSender};
use crate::base::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct SendIbcMessagesToChain;

#[async_trait]
impl<Context, Target, TargetChain, Message, Event, Error> IbcMessageSender<Context, Target>
    for SendIbcMessagesToChain
where
    Message: Async,
    Event: Async,
    Context: RelayContext<Error = Error>,
    Target: ChainTarget<Context, TargetChain = TargetChain>,
    TargetChain: HasMessageSender,
    TargetChain:
        IbcChainContext<Target::CounterpartyChain, Message = Message, Event = Event, Error = Error>,
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

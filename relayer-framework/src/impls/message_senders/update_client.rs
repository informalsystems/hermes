use alloc::collections::BTreeSet;
use async_trait::async_trait;

use crate::std_prelude::*;
use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message::IbcMessage;
use crate::traits::messages::update_client::{UpdateClientContext, UpdateClientMessageBuilder};
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;

pub struct SendIbcMessagesWithUpdateClient<Sender>(pub Sender);

#[async_trait]
impl<Sender, Context, Target, Height, TargetChain, CounterpartyChain, Message, Event>
    IbcMessageSender<Context, Target> for SendIbcMessagesWithUpdateClient<Sender>
where
    Context: RelayContext,
    Target: ChainTarget<Context, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    Sender: IbcMessageSender<Context, Target>,
    TargetChain: IbcChainContext<CounterpartyChain, IbcMessage = Message, IbcEvent = Event>,
    CounterpartyChain: IbcChainContext<TargetChain, Height = Height>,
    Context: UpdateClientContext<Target>,
    Message: IbcMessage<CounterpartyChain> + Async,
    Height: Ord + Async,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        let source_heights: BTreeSet<Height> = messages
            .iter()
            .map(|message| message.source_height().into_iter())
            .flatten()
            .collect();

        let mut in_messages = Vec::new();

        for height in source_heights {
            let messages =
                Context::UpdateClientMessageBuilder::build_update_client_messages(context, &height)
                    .await?;
            in_messages.extend(messages);
        }

        let update_messages_count = in_messages.len();

        in_messages.extend(messages);

        let in_events = Sender::send_messages(context, in_messages).await?;

        let events = in_events.into_iter().take(update_messages_count).collect();

        Ok(events)
    }
}

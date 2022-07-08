use async_trait::async_trait;
use core::marker::PhantomData;

use crate::traits::chain_context::IbcChainContext;
use crate::traits::core::Async;
use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message::IbcMessage;
use crate::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;

pub struct SendIbcMessagesWithUpdateClient<Sender>(PhantomData<Sender>);

#[async_trait]
impl<Sender, Context, Target, Height, TargetChain, CounterpartyChain, Message, Event>
    IbcMessageSender<Context, Target> for SendIbcMessagesWithUpdateClient<Sender>
where
    Context: RelayContext,
    Target: ChainTarget<Context, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    Sender: IbcMessageSender<Context, Target>,
    TargetChain: IbcChainContext<CounterpartyChain, IbcMessage = Message, IbcEvent = Event>,
    CounterpartyChain: IbcChainContext<TargetChain, Height = Height>,
    Context: UpdateClientMessageBuilder<Context, Target>,
    Message: IbcMessage<CounterpartyChain> + Async,
    Height: Ord + Async,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        let min_source_height = messages
            .iter()
            .map(|message| message.source_height())
            .reduce(|height1, height2| match (height1, height2) {
                (Some(h1), Some(h2)) => {
                    if h1 > h2 {
                        Some(h1)
                    } else {
                        Some(h2)
                    }
                }
                (Some(h1), None) => Some(h1),
                (None, h2) => h2,
            })
            .flatten();

        match min_source_height {
            Some(height) => {
                let mut in_messages = context.build_update_client_messages(height).await?;

                let update_messages_count = in_messages.len();

                in_messages.extend(messages);

                let in_events = Sender::send_messages(context, in_messages).await?;

                let events = in_events.into_iter().take(update_messages_count).collect();

                Ok(events)
            }
            None => Sender::send_messages(context, messages).await,
        }
    }
}

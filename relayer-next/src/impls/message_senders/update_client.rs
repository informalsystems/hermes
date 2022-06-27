use async_trait::async_trait;

use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message::IbcMessage as _;
use crate::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::traits::relay_types::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{Height, IbcEvent, IbcMessage};

pub struct MessageSenderWithUpdateClient<Sender> {
    pub sender: Sender,
}

#[async_trait]
impl<Sender, Context, Target> IbcMessageSender<Context, Target>
    for MessageSenderWithUpdateClient<Sender>
where
    Context: RelayContext,
    Target: ChainTarget<Context::RelayTypes>,
    Sender: IbcMessageSender<Context, Target>,
    Context: UpdateClientMessageBuilder<Context::RelayTypes, Target>,
    Height<Target::CounterpartyChain>: Ord,
{
    async fn send_messages(
        &self,
        context: &Context,
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Context::Error>
    {
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

                let in_events = self.sender.send_messages(context, in_messages).await?;

                let events = in_events.into_iter().take(update_messages_count).collect();

                Ok(events)
            }
            None => self.sender.send_messages(context, messages).await,
        }
    }
}

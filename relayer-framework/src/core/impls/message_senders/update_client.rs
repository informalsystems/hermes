use alloc::collections::BTreeSet;
use async_trait::async_trait;

use crate::core::traits::contexts::chain::IbcChainContext;
use crate::core::traits::contexts::relay::RelayContext;
use crate::core::traits::core::Async;
use crate::core::traits::ibc_message_sender::IbcMessageSender;
use crate::core::traits::messages::update_client::HasUpdateClientMessageBuilder;
use crate::core::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct SendIbcMessagesWithUpdateClient<Sender>(pub Sender);

#[async_trait]
impl<Sender, Context, Target, Height, TargetChain, CounterpartyChain, Message, Event>
    IbcMessageSender<Context, Target> for SendIbcMessagesWithUpdateClient<Sender>
where
    Context: RelayContext,
    Target: ChainTarget<Context, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    Sender: IbcMessageSender<Context, Target>,
    TargetChain: IbcChainContext<CounterpartyChain, Message = Message, Event = Event>,
    CounterpartyChain: IbcChainContext<TargetChain, Height = Height>,
    Context: HasUpdateClientMessageBuilder<Target>,
    Height: Ord + Async,
    Message: Async,
{
    async fn send_messages(
        context: &Context,
        messages: Vec<Message>,
    ) -> Result<Vec<Vec<Event>>, Context::Error> {
        let source_heights: BTreeSet<Height> = messages
            .iter()
            .flat_map(|message| TargetChain::counterparty_message_height(message).into_iter())
            .collect();

        let mut in_messages = Vec::new();

        for height in source_heights {
            let messages = context
                .build_update_client_messages(Target::default(), &height)
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

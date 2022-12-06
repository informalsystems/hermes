use alloc::collections::BTreeSet;
use async_trait::async_trait;

use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::core::traits::sync::Async;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct SendIbcMessagesWithUpdateClient<Sender>(pub Sender);

#[async_trait]
impl<Sender, Context, Target, Height, TargetChain, CounterpartyChain, Message, Event>
    IbcMessageSender<Context, Target> for SendIbcMessagesWithUpdateClient<Sender>
where
    Context: HasRelayTypes,
    Target: ChainTarget<Context, TargetChain = TargetChain, CounterpartyChain = CounterpartyChain>,
    Sender: IbcMessageSender<Context, Target>,
    TargetChain: HasIbcChainTypes<CounterpartyChain, Message = Message, Event = Event>,
    CounterpartyChain: HasIbcChainTypes<TargetChain, Height = Height>,
    Context: CanBuildUpdateClientMessage<Target>,
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

        let events = in_events.into_iter().skip(update_messages_count).collect();

        Ok(events)
    }
}

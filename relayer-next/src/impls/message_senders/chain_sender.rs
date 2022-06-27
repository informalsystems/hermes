use async_trait::async_trait;

use crate::traits::ibc_message_sender::IbcMessageSender;
use crate::traits::message::IbcMessage as _;
use crate::traits::message_sender::MessageSenderContext;
use crate::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::traits::relay_types::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{Height, IbcEvent, IbcMessage};

pub struct SendIbcMessageToChain;

#[async_trait]
impl<Context, Target> IbcMessageSender<Context, Target> for SendIbcMessageToChain
where
    Context: RelayContext,
    Target: ChainTarget<Context>,
    Target::TargetChain: MessageSenderContext,
{
    async fn send_messages(
        &self,
        context: &Context,
        messages: Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>,
    ) -> Result<Vec<Vec<IbcEvent<Target::TargetChain, Target::CounterpartyChain>>>, Context::Error>
    {
        todo!()
    }
}

use async_trait::async_trait;

use crate::base::chain::traits::types::ibc::HasIbcChainTypes;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::batch::traits::channel::HasMessageBatchSender;
use crate::full::batch::traits::send_messages_from_batch::CanSendIbcMessagesFromBatchWorker;
use crate::full::runtime::traits::channel::CanUseChannels;
use crate::full::runtime::traits::channel_once::{CanCreateChannelsOnce, CanUseChannelsOnce};
use crate::std_prelude::*;

pub struct SendMessagesToBatchWorker;

#[async_trait]
impl<Relay, Target, TargetChain, Runtime> IbcMessageSender<Relay, Target>
    for SendMessagesToBatchWorker
where
    Relay: HasRelayTypes,
    Relay: CanSendIbcMessagesFromBatchWorker<Target>,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
    TargetChain: HasRuntime<Runtime = Runtime>,
    Runtime: CanCreateChannelsOnce + CanUseChannels + CanUseChannelsOnce,
    Relay: HasMessageBatchSender<Target>,
{
    async fn send_messages(
        context: &Relay,
        messages: Vec<TargetChain::Message>,
    ) -> Result<Vec<Vec<TargetChain::Event>>, Relay::Error> {
        let (result_sender, result_receiver) = Runtime::new_channel_once();

        let message_sender = context.get_batch_sender();

        Runtime::send(message_sender, (messages, result_sender))
            .map_err(TargetChain::runtime_error)
            .map_err(Target::target_chain_error)?;

        let events = Runtime::receive_once(result_receiver)
            .await
            .map_err(TargetChain::runtime_error)
            .map_err(Target::target_chain_error)??;

        Ok(events)
    }
}

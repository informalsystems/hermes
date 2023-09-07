use async_trait::async_trait;
use ibc_relayer_components::chain::traits::types::ibc::HasIbcChainTypes;
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::components::ibc_message_sender::{
    CanSendIbcMessages, IbcMessageSender,
};
use ibc_relayer_components::relay::traits::target::ChainTarget;
use ibc_relayer_components::runtime::traits::runtime::HasRuntime;

use crate::batch::traits::channel::HasMessageBatchSender;
use crate::batch::types::sink::BatchWorkerSink;
use crate::runtime::traits::channel::CanUseChannels;
use crate::runtime::traits::channel_once::{CanCreateChannelsOnce, CanUseChannelsOnce};
use crate::std_prelude::*;

pub struct SendMessagesToBatchWorker;

#[async_trait]
impl<Relay, Sink, Target, TargetChain, Runtime> IbcMessageSender<Relay, Sink, Target>
    for SendMessagesToBatchWorker
where
    Relay: HasRelayChains,
    Relay: CanSendIbcMessages<BatchWorkerSink, Target>,
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

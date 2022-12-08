use async_trait::async_trait;

use crate::base::chain::traits::message_sender::CanSendMessages;
use crate::base::chain::traits::types::HasIbcChainTypes;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

pub struct SendIbcMessagesToChain;

#[async_trait]
impl<Relay, Target, TargetChain> IbcMessageSender<Relay, Target> for SendIbcMessagesToChain
where
    Relay: HasRelayTypes,
    Target: ChainTarget<Relay, TargetChain = TargetChain>,
    TargetChain: CanSendMessages,
    TargetChain: HasIbcChainTypes<Target::CounterpartyChain>,
{
    async fn send_messages(
        relay: &Relay,
        messages: Vec<TargetChain::Message>,
    ) -> Result<Vec<Vec<TargetChain::Event>>, Relay::Error> {
        let events = Target::target_chain(relay)
            .send_messages(messages)
            .await
            .map_err(Target::target_chain_error)?;

        Ok(events)
    }
}

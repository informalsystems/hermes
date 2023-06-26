use async_trait::async_trait;
use ibc_relayer_components::chain::types::aliases::{Event, Message};
use ibc_relayer_components::relay::traits::chains::HasRelayChains;
use ibc_relayer_components::relay::traits::target::ChainTarget;

use crate::std_prelude::*;

#[async_trait]
pub trait CanSendIbcMessagesFromBatchWorker<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    async fn send_messages_from_batch_worker(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error>;
}

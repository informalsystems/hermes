use async_trait::async_trait;

use crate::base::chain::types::aliases::{Event, Message};
use crate::base::relay::traits::target::ChainTarget;
use crate::base::relay::traits::types::HasRelayTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanSendIbcMessagesFromBatchWorker<Target>: HasRelayTypes
where
    Target: ChainTarget<Self>,
{
    async fn send_messages_from_batch_worker(
        &self,
        messages: Vec<Message<Target::TargetChain>>,
    ) -> Result<Vec<Vec<Event<Target::TargetChain>>>, Self::Error>;
}

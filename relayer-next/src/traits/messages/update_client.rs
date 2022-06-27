use async_trait::async_trait;

use crate::traits::relay_context::RelayContext;
use crate::traits::target::ChainTarget;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
pub trait UpdateClientMessageBuilder<Relay, Target>
where
    Relay: RelayContext,
    Target: ChainTarget<Relay>,
{
    async fn build_update_client_messages(
        &self,
        height: Height<Target::CounterpartyChain>,
    ) -> Result<Vec<IbcMessage<Target::TargetChain, Target::CounterpartyChain>>, Relay::Error>;
}

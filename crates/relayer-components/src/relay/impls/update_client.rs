use async_trait::async_trait;

use crate::chain::traits::message_sender::CanSendMessages;
use crate::chain::types::aliases::Height;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::messages::update_client::CanBuildUpdateClientMessage;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

#[async_trait]
pub trait CanSendUpdateClientMessage<Target>: HasRelayChains
where
    Target: ChainTarget<Self>,
{
    async fn send_update_client_messages(
        &self,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<(), Self::Error>;
}

#[async_trait]
impl<Relay, Target> CanSendUpdateClientMessage<Target> for Relay
where
    Relay: CanBuildUpdateClientMessage<Target>,
    Target: ChainTarget<Relay>,
    Target::TargetChain: CanSendMessages,
{
    async fn send_update_client_messages(
        &self,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<(), Self::Error> {
        let messages = self.build_update_client_messages(target, height).await?;
        Target::target_chain(self)
            .send_messages(messages)
            .await
            .map_err(Target::target_chain_error)?;

        Ok(())
    }
}

use async_trait::async_trait;

use crate::chain::types::aliases::{Height, Message};
use crate::relay::impls::client::update::BuildUpdateClientMessages;
use crate::relay::impls::messages::skip_update_client::SkipUpdateClient;
use crate::relay::impls::messages::wait_update_client::WaitUpdateClient;
use crate::relay::traits::chains::HasRelayChains;
use crate::relay::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::relay::traits::target::ChainTarget;
use crate::std_prelude::*;

pub struct DefaultComponents;

#[async_trait]
impl<Relay, Target> UpdateClientMessageBuilder<Relay, Target> for DefaultComponents
where
    Relay: HasRelayChains,
    Target: ChainTarget<Relay>,
    SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>:
        UpdateClientMessageBuilder<Relay, Target>,
{
    async fn build_update_client_messages(
        relay: &Relay,
        target: Target,
        height: &Height<Target::CounterpartyChain>,
    ) -> Result<Vec<Message<Target::TargetChain>>, Relay::Error> {
        <SkipUpdateClient<WaitUpdateClient<BuildUpdateClientMessages>>>::build_update_client_messages(relay, target, height).await
    }
}

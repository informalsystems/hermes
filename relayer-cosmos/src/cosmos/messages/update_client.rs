use async_trait::async_trait;
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::traits::chain_context::{ChainContext, IbcChainContext};
use ibc_relayer_framework::traits::messages::update_client::UpdateClientMessageBuilder;
use ibc_relayer_framework::traits::target::ChainTarget;

use crate::cosmos::error::Error;
use crate::cosmos::handler::CosmosRelayHandler;
use crate::cosmos::message::CosmosIbcMessage;
use crate::cosmos::target::CosmosChainTarget;

#[async_trait]
impl<SrcChain, DstChain, Target>
    UpdateClientMessageBuilder<CosmosRelayHandler<SrcChain, DstChain>, Target>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: ChainTarget<CosmosRelayHandler<SrcChain, DstChain>>,
    Self: CosmosChainTarget<SrcChain, DstChain, Target>,
    Target::CounterpartyChain: ChainContext<Height = Height>,
    Target::TargetChain: IbcChainContext<Target::CounterpartyChain, IbcMessage = CosmosIbcMessage>,
{
    async fn build_update_client_messages(
        &self,
        height: Height,
    ) -> Result<Vec<CosmosIbcMessage>, Error> {
        let messages = self
            .target_foreign_client()
            .build_update_client_with_trusted(height, None)
            .map_err(Error::foreign_client)?;

        let ibc_messages = messages
            .into_iter()
            .map(|update_message| {
                CosmosIbcMessage::new(Some(height), move |signer| {
                    let mut update_message = update_message.clone();
                    update_message.signer = signer.clone();
                    Ok(update_message.to_any())
                })
            })
            .collect();

        Ok(ibc_messages)
    }
}

use async_trait::async_trait;
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer_framework::impls::messages::skip_update_client::SkipUpdateClient;
use ibc_relayer_framework::impls::messages::wait_update_client::WaitUpdateClient;
use ibc_relayer_framework::traits::messages::update_client::{
    UpdateClientContext, UpdateClientMessageBuilder,
};

use crate::cosmos::error::Error;
use crate::cosmos::handler::CosmosRelayHandler;
use crate::cosmos::message::CosmosIbcMessage;
use crate::cosmos::target::CosmosChainTarget;

pub struct CosmosUpdateClient;

impl<SrcChain, DstChain, Target> UpdateClientContext<Target>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: CosmosChainTarget<SrcChain, DstChain>,
{
    type UpdateClientMessageBuilder = SkipUpdateClient<WaitUpdateClient<CosmosUpdateClient>>;
}

#[async_trait]
impl<SrcChain, DstChain, Target>
    UpdateClientMessageBuilder<CosmosRelayHandler<SrcChain, DstChain>, Target>
    for CosmosUpdateClient
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
    Target: CosmosChainTarget<SrcChain, DstChain>,
{
    async fn build_update_client_messages(
        context: &CosmosRelayHandler<SrcChain, DstChain>,
        height: &Height,
    ) -> Result<Vec<CosmosIbcMessage>, Error> {
        let messages = Target::target_foreign_client(context)
            .build_update_client_with_trusted(height.increment(), None)
            .map_err(Error::foreign_client)?;

        let ibc_messages = messages
            .into_iter()
            .map(|update_message| {
                CosmosIbcMessage::new(Some(*height), move |signer| {
                    let mut update_message = update_message.clone();
                    update_message.signer = signer.clone();
                    Ok(update_message.to_any())
                })
            })
            .collect();

        Ok(ibc_messages)
    }
}

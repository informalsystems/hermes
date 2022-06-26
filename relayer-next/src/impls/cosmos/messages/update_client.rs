use async_trait::async_trait;
use ibc::Height;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::handler::CosmosRelayHandler;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::impls::cosmos::relay_types::CosmosRelayTypes;
use crate::traits::messages::update_client::UpdateClientMessageBuilder;

#[async_trait]
impl<SrcChain, DstChain> UpdateClientMessageBuilder<CosmosRelayTypes>
    for CosmosRelayHandler<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    async fn build_update_client_messages(
        &self,
        height: Height,
    ) -> Result<Vec<CosmosIbcMessage>, Error> {
        let messages = self
            .src_to_dst_client
            .build_update_client_with_trusted(height, None)
            .map_err(Error::foreign_client)?;

        let ibc_messages = messages
            .into_iter()
            .map(|any| CosmosIbcMessage::new(Some(height), |_| Ok(any)))
            .collect();

        Ok(ibc_messages)
    }
}

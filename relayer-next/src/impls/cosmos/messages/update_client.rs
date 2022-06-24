use async_trait::async_trait;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::impls::cosmos::relay_context::CosmosRelayContext;
use crate::traits::messages::update_client::UpdateClientMessageBuilder;
use crate::types::aliases::{Height, IbcMessage};

#[async_trait]
impl<SrcChain, DstChain> UpdateClientMessageBuilder for CosmosRelayContext<SrcChain, DstChain>
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    async fn build_update_client_messages(
        &self,
        height: Height<Self::SrcChain>,
    ) -> Result<Vec<IbcMessage<Self::DstChain, Self::SrcChain>>, Self::Error> {
        let messages = self
            .foreign_client_src_to_dst
            .build_update_client_with_trusted(height, None)
            .map_err(Error::foreign_client)?;

        let ibc_messages = messages
            .into_iter()
            .map(|any| CosmosIbcMessage::new(Some(height), |_| Ok(any)))
            .collect();

        Ok(ibc_messages)
    }
}

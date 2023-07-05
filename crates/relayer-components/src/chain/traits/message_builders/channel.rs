use async_trait::async_trait;

use crate::chain::traits::types::channel::HasInitChannelOptionsType;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildChannelHandshakeMessages<Counterparty>:
    HasInitChannelOptionsType<Counterparty> + HasErrorType
{
    async fn build_channel_open_init_message(
        &self,
        init_channel_options: &Self::InitChannelOptions,
    ) -> Result<Self::Message, Self::Error>;
}

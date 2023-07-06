use async_trait::async_trait;

use crate::chain::traits::types::channel::{
    HasChannelHandshakePayloads, HasInitChannelOptionsType,
};
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildChannelHandshakePayloads<Counterparty>:
    HasChannelHandshakePayloads<Counterparty> + HasErrorType
{
    async fn build_channel_open_try_payload(
        &self,
        height: &Self::Height,
        port_id: &Self::PortId,
        channel_id: &Self::ChannelId,
    ) -> Result<Self::ChannelOpenTryPayload, Self::Error>;
}

#[async_trait]
pub trait CanBuildChannelHandshakeMessages<Counterparty>:
    HasInitChannelOptionsType<Counterparty> + HasErrorType
where
    Counterparty: HasChannelHandshakePayloads<Self>,
{
    async fn build_channel_open_init_message(
        &self,
        init_channel_options: &Self::InitChannelOptions,
    ) -> Result<Self::Message, Self::Error>;

    async fn build_channel_open_try_message(
        &self,
        counterparty_payload: Counterparty::ChannelOpenTryPayload,
    ) -> Result<Self::Message, Self::Error>;
}

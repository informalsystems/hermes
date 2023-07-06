use async_trait::async_trait;

use ibc_relayer_components::relay::impls::channel::open_ack::RelayChannelOpenAck;
use ibc_relayer_components::relay::impls::channel::open_confirm::RelayChannelOpenConfirm;
use ibc_relayer_components::relay::impls::channel::open_init::{
    InitializeChannel, InjectMissingChannelInitEventError,
};
use ibc_relayer_components::relay::impls::channel::open_try::{
    InjectMissingChannelTryEventError, RelayChannelOpenTry,
};
use ibc_relayer_components::relay::traits::channel::open_ack::{
    CanRelayChannelOpenAck, ChannelOpenAckRelayer,
};
use ibc_relayer_components::relay::traits::channel::open_confirm::{
    CanRelayChannelOpenConfirm, ChannelOpenConfirmRelayer,
};
use ibc_relayer_components::relay::traits::channel::open_init::{
    CanInitChannel, ChannelInitializer,
};
use ibc_relayer_components::relay::traits::channel::open_try::{
    CanRelayChannelOpenTry, ChannelOpenTryRelayer,
};

use crate::one_for_all::traits::chain::{OfaChain, OfaIbcChain};
use crate::one_for_all::{traits::relay::OfaRelay, types::relay::OfaRelayWrapper};
use crate::std_prelude::*;

impl<Relay> InjectMissingChannelInitEventError for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn missing_channel_init_event_error(&self) -> Relay::Error {
        self.relay.missing_channel_init_event_error()
    }
}

impl<Relay> InjectMissingChannelTryEventError for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    fn missing_channel_try_event_error(
        &self,
        src_channel_id: &<Relay::SrcChain as OfaChain>::ChannelId,
    ) -> Relay::Error {
        self.relay.missing_channel_try_event_error(src_channel_id)
    }
}

#[async_trait]
impl<Relay> CanInitChannel for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn init_channel(
        &self,
        src_port_id: &<Relay::SrcChain as OfaChain>::PortId,
        dst_port_id: &<Relay::DstChain as OfaChain>::PortId,
        init_channel_options: &<Relay::SrcChain as OfaIbcChain<Relay::DstChain>>::InitChannelOptions,
    ) -> Result<<Relay::SrcChain as OfaChain>::ChannelId, Self::Error> {
        InitializeChannel::init_channel(self, src_port_id, dst_port_id, init_channel_options).await
    }
}

#[async_trait]
impl<Relay> CanRelayChannelOpenTry for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn relay_channel_open_try(
        &self,
        dst_port_id: &<Relay::DstChain as OfaChain>::PortId,
        src_port_id: &<Relay::SrcChain as OfaChain>::PortId,
        src_channel_id: &<Relay::SrcChain as OfaChain>::ChannelId,
    ) -> Result<<Relay::DstChain as OfaChain>::ChannelId, Self::Error> {
        RelayChannelOpenTry::relay_channel_open_try(self, dst_port_id, src_port_id, src_channel_id)
            .await
    }
}

#[async_trait]
impl<Relay> CanRelayChannelOpenAck for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn relay_channel_open_ack(
        &self,
        src_port_id: &<Relay::SrcChain as OfaChain>::PortId,
        src_channel_id: &<Relay::SrcChain as OfaChain>::ChannelId,
        dst_port_id: &<Relay::DstChain as OfaChain>::PortId,
        dst_channel_id: &<Relay::DstChain as OfaChain>::ChannelId,
    ) -> Result<(), Self::Error> {
        RelayChannelOpenAck::relay_channel_open_ack(
            self,
            src_port_id,
            src_channel_id,
            dst_port_id,
            dst_channel_id,
        )
        .await
    }
}

#[async_trait]
impl<Relay> CanRelayChannelOpenConfirm for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay,
{
    async fn relay_channel_open_confirm(
        &self,
        dst_port_id: &<Relay::DstChain as OfaChain>::PortId,
        dst_channel_id: &<Relay::DstChain as OfaChain>::ChannelId,
        src_port_id: &<Relay::SrcChain as OfaChain>::PortId,
        src_channel_id: &<Relay::SrcChain as OfaChain>::ChannelId,
    ) -> Result<(), Self::Error> {
        RelayChannelOpenConfirm::relay_channel_open_confirm(
            self,
            dst_port_id,
            dst_channel_id,
            src_port_id,
            src_channel_id,
        )
        .await
    }
}

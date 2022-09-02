use async_trait::async_trait;
use core::marker::PhantomData;

use crate::core::traits::contexts::chain::ChainContext;
use crate::core::traits::contexts::relay::RelayContext;
use crate::std_prelude::*;

// pub trait FilterContext: RelayContext {
//     fn should_relay(&self, packet: &Self::Packet) -> bool;
// }

#[async_trait]
pub trait PacketFilter<Relay>
where
    Relay: RelayContext,
{
    async fn should_relay_packet(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error>;
}

#[async_trait]
pub trait HasPacketFilter: RelayContext {
    type PacketFilter: PacketFilter<Self>;

    async fn should_relay_packet(&self, packet: &Self::Packet) -> Result<bool, Self::Error> {
        Self::PacketFilter::should_relay_packet(self, packet).await
    }
}

#[async_trait]
pub trait PacketAccountQuerier<Relay: RelayContext> {
    async fn query_packet_account(
        relay: &Relay,
        packet: &Relay::Packet,
    ) -> Result<<Relay::SrcChain as ChainContext>::Signer, Relay::Error>;
}

pub struct PacketAccountFilter;

pub struct ChannelFilter;

pub struct AndPacketFilter<FilterA, FilterB>(PhantomData<(FilterA, FilterB)>);

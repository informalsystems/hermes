use async_trait::async_trait;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc_relayer::config::filter::PacketFilter as CosmosFilter;
use ibc_relayer_framework::core::traits::contexts::chain::IbcChainContext;
use ibc_relayer_framework::core::traits::contexts::filter::PacketFilter;
use ibc_relayer_framework::core::traits::contexts::relay::RelayContext;

pub struct CosmosChannelFilter {
    pub filter: CosmosFilter,
}

impl CosmosChannelFilter {
    pub fn new(filter: CosmosFilter) -> Self {
        Self { filter }
    }

    pub fn filter(&self) -> &CosmosFilter {
        &self.filter
    }
}

#[async_trait]
impl<Relay> PacketFilter<Relay> for CosmosChannelFilter
where Relay: RelayContext,
<<Relay as RelayContext>::SrcChain as IbcChainContext<<Relay as RelayContext>::DstChain>>::ChannelId: Into<ChannelId>,
<<Relay as RelayContext>::SrcChain as IbcChainContext<<Relay as RelayContext>::DstChain>>::ChannelId: Clone,
<<Relay as RelayContext>::SrcChain as IbcChainContext<<Relay as RelayContext>::DstChain>>::PortId: Into<PortId>,
<<Relay as RelayContext>::SrcChain as IbcChainContext<<Relay as RelayContext>::DstChain>>::PortId: Clone,

{
    async fn should_relay_packet(
        &self,
        packet: &Relay::Packet,
    ) -> Result<bool, Relay::Error> {
        let src_channel = <Relay as RelayContext>::packet_src_channel_id(packet).clone();
        let src_port = <Relay as RelayContext>::packet_src_port(packet).clone();
        Ok(self.filter().is_allowed(&src_port.into(), &src_channel.into()))
    }
}

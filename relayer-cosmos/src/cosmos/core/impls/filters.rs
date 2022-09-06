use async_trait::async_trait;
use ibc_relayer::config::filter::PacketFilter as IbcChannelFilter;
use ibc_relayer_framework::core::traits::contexts::error::HasError;
use ibc_relayer_framework::core::traits::contexts::filter::PacketFilter;
use ibc_relayer_framework::core::traits::contexts::relay::RelayContext;
use ibc_relayer_framework::one_for_all::traits::relay::OfaRelayContext;

use crate::cosmos::core::traits::relay::CosmosRelay;
use crate::cosmos::core::types::relay::CosmosRelayContext;

pub struct CosmosChannelFilter {
    pub filter: IbcChannelFilter,
}

impl CosmosChannelFilter {
    pub fn new(filter: IbcChannelFilter) -> Self {
        Self { filter }
    }

    pub fn channel_filter(&self) -> &IbcChannelFilter {
        &self.filter
    }
}

#[async_trait]
impl<Relay> PacketFilter<OfaRelayContext<CosmosRelayContext<Relay>>> for CosmosChannelFilter
where
    Relay: CosmosRelay,
{
    async fn should_relay_packet(
        &self,
        packet: &<OfaRelayContext<CosmosRelayContext<Relay>> as RelayContext>::Packet,
    ) -> Result<bool, <OfaRelayContext<CosmosRelayContext<Relay>> as HasError>::Error> {
        let src_channel =
            <OfaRelayContext<CosmosRelayContext<Relay>>>::packet_src_channel_id(packet).clone();
        let src_port =
            <OfaRelayContext<CosmosRelayContext<Relay>>>::packet_src_port(packet).clone();
        Ok(self.channel_filter().is_allowed(&src_port, &src_channel))
    }
}

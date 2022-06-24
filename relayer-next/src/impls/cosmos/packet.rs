use ibc::core::ics04_channel::packet::Packet;
use ibc_relayer::chain::handle::ChainHandle;

use crate::impls::cosmos::chain_context::CosmosChainContext;
use crate::traits::packet::IbcPacket;
use crate::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};

impl<SrcChain, DstChain> IbcPacket<CosmosChainContext<SrcChain>, CosmosChainContext<DstChain>>
    for Packet
where
    SrcChain: ChainHandle,
    DstChain: ChainHandle,
{
    fn source_port(&self) -> &PortId<CosmosChainContext<SrcChain>, CosmosChainContext<DstChain>> {
        &self.source_port
    }

    fn source_channel_id(
        &self,
    ) -> &ChannelId<CosmosChainContext<SrcChain>, CosmosChainContext<DstChain>> {
        &self.source_channel
    }

    fn destination_port(
        &self,
    ) -> &PortId<CosmosChainContext<DstChain>, CosmosChainContext<SrcChain>> {
        &self.destination_port
    }

    fn destination_channel_id(
        &self,
    ) -> &ChannelId<CosmosChainContext<DstChain>, CosmosChainContext<SrcChain>> {
        &self.destination_channel
    }

    fn sequence(&self) -> &Sequence<CosmosChainContext<SrcChain>, CosmosChainContext<DstChain>> {
        &self.sequence
    }

    fn timeout_height(&self) -> &Height<CosmosChainContext<DstChain>> {
        &self.timeout_height
    }

    fn timeout_timestamp(&self) -> &Timestamp<CosmosChainContext<DstChain>> {
        &self.timeout_timestamp
    }
}

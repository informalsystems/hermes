use ibc::core::ics04_channel::packet::Packet;

use crate::impls::cosmos::chain_types::CosmosChainTypes;
use crate::traits::packet::IbcPacket;
use crate::types::aliases::{ChannelId, Height, PortId, Sequence, Timestamp};

impl IbcPacket<CosmosChainTypes, CosmosChainTypes> for Packet {
    fn source_port(&self) -> &PortId<CosmosChainTypes, CosmosChainTypes> {
        &self.source_port
    }

    fn source_channel_id(&self) -> &ChannelId<CosmosChainTypes, CosmosChainTypes> {
        &self.source_channel
    }

    fn destination_port(&self) -> &PortId<CosmosChainTypes, CosmosChainTypes> {
        &self.destination_port
    }

    fn destination_channel_id(&self) -> &ChannelId<CosmosChainTypes, CosmosChainTypes> {
        &self.destination_channel
    }

    fn sequence(&self) -> &Sequence<CosmosChainTypes, CosmosChainTypes> {
        &self.sequence
    }

    fn timeout_height(&self) -> &Height<CosmosChainTypes> {
        &self.timeout_height
    }

    fn timeout_timestamp(&self) -> &Timestamp<CosmosChainTypes> {
        &self.timeout_timestamp
    }
}

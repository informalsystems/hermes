use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics04_channel::timeout::TimeoutHeight;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_relayer_framework::traits::core::Async;
use ibc_relayer_framework::traits::packet::IbcPacket;

use crate::cosmos::context::chain::CosmosChainContext;

impl<SrcChain, DstChain> IbcPacket<CosmosChainContext<SrcChain>, CosmosChainContext<DstChain>>
    for Packet
where
    SrcChain: Async,
    DstChain: Async,
{
    fn source_port(&self) -> &PortId {
        &self.source_port
    }

    fn source_channel_id(&self) -> &ChannelId {
        &self.source_channel
    }

    fn destination_port(&self) -> &PortId {
        &self.destination_port
    }

    fn destination_channel_id(&self) -> &ChannelId {
        &self.destination_channel
    }

    fn sequence(&self) -> &Sequence {
        &self.sequence
    }

    fn timeout_height(&self) -> Option<Height> {
        match self.timeout_height {
            TimeoutHeight::Never => None,
            TimeoutHeight::At(h) => Some(h),
        }
    }

    fn timeout_timestamp(&self) -> &Timestamp {
        &self.timeout_timestamp
    }
}

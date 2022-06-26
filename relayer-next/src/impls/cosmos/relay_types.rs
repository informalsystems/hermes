use core::fmt::Debug;
use ibc::core::ics04_channel::packet::Packet;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::timestamp::Timestamp;
use ibc::Height;

use crate::impls::cosmos::chain_types::CosmosChainTypes;
use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::traits::relay_types::RelayTypes;

#[derive(Debug, Clone)]
pub struct CosmosRelayTypes;

impl RelayTypes for CosmosRelayTypes {
    type Error = Error;

    type SrcChain = CosmosChainTypes;

    type DstChain = CosmosChainTypes;

    type SrcHeight = Height;

    type DstHeight = Height;

    type SrcTimestamp = Timestamp;

    type DstTimestamp = Timestamp;

    type SrcMessage = CosmosIbcMessage;

    type DstMessage = CosmosIbcMessage;

    type SrcPortId = PortId;

    type DstPortId = PortId;

    type SrcChannelId = ChannelId;

    type DstChannelId = ChannelId;

    type SrcSequence = Sequence;

    type DstSequence = Sequence;

    type SrcIbcEvent = IbcEvent;

    type DstIbcEvent = IbcEvent;

    type Packet = Packet;
}

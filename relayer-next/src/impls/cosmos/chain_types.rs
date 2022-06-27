use core::fmt::Debug;
use ibc::core::ics04_channel::packet::Sequence;
use ibc::core::ics24_host::identifier::{ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc::timestamp::Timestamp;
use ibc::Height;

use crate::impls::cosmos::error::Error;
use crate::impls::cosmos::message::CosmosIbcMessage;
use crate::traits::chain_types::{ChainTypes, IbcChainTypes};
use crate::traits::core::ErrorContext;

#[derive(Debug, Clone)]
pub struct CosmosChainTypes;

impl ErrorContext for CosmosChainTypes {
    type Error = Error;
}

impl ChainTypes for CosmosChainTypes {
    type Height = Height;

    type Timestamp = Timestamp;

    type Message = CosmosIbcMessage;

    type Event = IbcEvent;
}

impl IbcChainTypes<CosmosChainTypes> for CosmosChainTypes {
    type ChannelId = ChannelId;

    type PortId = PortId;

    type Sequence = Sequence;

    type IbcMessage = CosmosIbcMessage;

    type IbcEvent = IbcEvent;
}

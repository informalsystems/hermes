use tendermint::abci::transaction::Hash;

use crate::events::IbcEventType;
use crate::ics02_client::client_consensus::QueryClientEventRequest;
use crate::ics02_client::height::Height;
use crate::ics04_channel::packet::Sequence;
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;

/// Used for queries and not yet standardized in channel's query.proto
#[derive(Clone, Debug)]
pub enum QueryTxRequest {
    Client(QueryClientEventRequest),
    Transaction(QueryTxHash),
}

#[derive(Clone, Debug)]
pub struct QueryTxHash(pub Hash);

/// Used to query a packet event, identified by `event_id`, for specific channel and sequences.
/// The query is preformed for the chain context at `height`.
#[derive(Clone, Debug)]
pub struct QueryPacketEventDataRequest {
    pub event_id: IbcEventType,
    pub source_channel_id: ChannelId,
    pub source_port_id: PortId,
    pub destination_channel_id: ChannelId,
    pub destination_port_id: PortId,
    pub sequences: Vec<Sequence>,
    pub height: Height,
}

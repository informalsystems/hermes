use crate::ics04_channel::channel::QueryPacketEventDataRequest;
use crate::ics07_tendermint::header::QueryHeaderRequest;

/// Used for queries and not yet standardized in channel's query.proto
#[derive(Clone, Debug)]
pub enum QueryTxRequest {
    Packet(QueryPacketEventDataRequest),
    Header(QueryHeaderRequest),
}

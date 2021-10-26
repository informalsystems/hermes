use tendermint::abci::transaction::Hash;

use crate::core::ics02_client::client_consensus::QueryClientEventRequest;
use crate::core::ics04_channel::channel::QueryPacketEventDataRequest;

/// Used for queries and not yet standardized in channel's query.proto
#[derive(Clone, Debug)]
pub enum QueryTxRequest {
    Packet(QueryPacketEventDataRequest),
    Client(QueryClientEventRequest),
    Transaction(QueryTxHash),
}

#[derive(Clone, Debug)]
pub enum QueryBlockRequest {
    Packet(QueryPacketEventDataRequest),
}

#[derive(Clone, Debug)]
pub struct QueryTxHash(pub Hash);

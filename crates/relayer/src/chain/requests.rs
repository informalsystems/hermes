use core::fmt::{self, Display};

use crate::error::Error;

use ibc_proto::cosmos::base::query::v1beta1::PageRequest as RawPageRequest;
use ibc_proto::ibc::core::channel::v1::{
    QueryChannelClientStateRequest as RawQueryChannelClientStateRequest,
    QueryChannelsRequest as RawQueryChannelsRequest,
    QueryConnectionChannelsRequest as RawQueryConnectionChannelsRequest,
    QueryNextSequenceReceiveRequest as RawQueryNextSequenceReceiveRequest,
    QueryPacketAcknowledgementsRequest as RawQueryPacketAcknowledgementsRequest,
    QueryPacketCommitmentsRequest as RawQueryPacketCommitmentsRequest,
    QueryUnreceivedAcksRequest as RawQueryUnreceivedAcksRequest,
    QueryUnreceivedPacketsRequest as RawQueryUnreceivedPacketsRequest,
};
use ibc_proto::ibc::core::client::v1::{
    QueryClientStatesRequest as RawQueryClientStatesRequest,
    QueryConsensusStatesRequest as RawQueryConsensusStatesRequest,
};
use ibc_proto::ibc::core::connection::v1::{
    QueryClientConnectionsRequest as RawQueryClientConnectionsRequest,
    QueryConnectionsRequest as RawQueryConnectionsRequest,
};
use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc_relayer_types::events::WithBlockDataType;
use ibc_relayer_types::Height;

use serde::{Deserialize, Serialize};
use tendermint::block::Height as TMBlockHeight;
use tendermint_rpc::abci::transaction::Hash as TxHash;
use tonic::metadata::AsciiMetadataValue;

/// Type to specify a height in a query. Specifically, this caters to the use
/// case where the user wants to query at whatever the latest height is, as
/// opposed to specifying a specific height.
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub enum QueryHeight {
    Latest,
    Specific(Height),
}

impl TryFrom<QueryHeight> for TMBlockHeight {
    type Error = Error;

    fn try_from(height_query: QueryHeight) -> Result<Self, Self::Error> {
        let height = match height_query {
            QueryHeight::Latest => 0u64,
            QueryHeight::Specific(height) => height.revision_height(),
        };

        Self::try_from(height).map_err(Error::invalid_height)
    }
}

impl TryFrom<QueryHeight> for AsciiMetadataValue {
    type Error = Error;

    fn try_from(height_query: QueryHeight) -> Result<Self, Self::Error> {
        let height = match height_query {
            QueryHeight::Latest => 0u64,
            QueryHeight::Specific(height) => height.revision_height(),
        };

        str::parse(&height.to_string()).map_err(Error::invalid_metadata)
    }
}

impl Display for QueryHeight {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            QueryHeight::Latest => write!(f, "latest height"),
            QueryHeight::Specific(height) => write!(f, "{}", height),
        }
    }
}

/// Defines a type to be used in select requests to specify whether or not a proof should be
/// returned along with the response.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum IncludeProof {
    Yes,
    No,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PageRequest {
    /// key is a value returned in PageResponse.next_key to begin
    /// querying the next page most efficiently. Only one of offset or key
    /// should be set.
    pub key: ::prost::alloc::vec::Vec<u8>,
    /// offset is a numeric offset that can be used when key is unavailable.
    /// It is less efficient than using key. Only one of offset or key should
    /// be set.
    pub offset: u64,
    /// limit is the total number of results to be returned in the result page.
    /// If left empty it will default to a value to be set by each app.
    pub limit: u64,
    /// count_total is set to true  to indicate that the result set should include
    /// a count of the total number of items available for pagination in UIs.
    /// count_total is only respected when offset is used. It is ignored when key
    /// is set.
    pub count_total: bool,
    /// reverse is set to true if results are to be returned in the descending order.
    pub reverse: bool,
}

impl PageRequest {
    pub fn all() -> PageRequest {
        PageRequest {
            limit: u64::MAX,
            ..Default::default()
        }
    }
}

impl From<PageRequest> for RawPageRequest {
    fn from(request: PageRequest) -> Self {
        RawPageRequest {
            key: request.key,
            offset: request.offset,
            limit: request.limit,
            count_total: request.count_total,
            reverse: request.reverse,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryClientStateRequest {
    pub client_id: ClientId,
    pub height: QueryHeight,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryClientStatesRequest {
    pub pagination: Option<PageRequest>,
}

impl From<QueryClientStatesRequest> for RawQueryClientStatesRequest {
    fn from(request: QueryClientStatesRequest) -> Self {
        RawQueryClientStatesRequest {
            pagination: request.pagination.map(|pagination| pagination.into()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryConsensusStateRequest {
    pub client_id: ClientId,
    pub consensus_height: Height,
    pub query_height: QueryHeight,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryUpgradedClientStateRequest {
    /// Height at which the chain is scheduled to halt for upgrade
    pub upgrade_height: Height,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryUpgradedConsensusStateRequest {
    /// Height at which the chain is scheduled to halt for upgrade
    pub upgrade_height: Height,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryConsensusStatesRequest {
    pub client_id: ClientId,
    pub pagination: Option<PageRequest>,
}

impl From<QueryConsensusStatesRequest> for RawQueryConsensusStatesRequest {
    fn from(request: QueryConsensusStatesRequest) -> Self {
        RawQueryConsensusStatesRequest {
            client_id: request.client_id.to_string(),
            pagination: request.pagination.map(|pagination| pagination.into()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryConnectionsRequest {
    pub pagination: Option<PageRequest>,
}

impl From<QueryConnectionsRequest> for RawQueryConnectionsRequest {
    fn from(request: QueryConnectionsRequest) -> Self {
        RawQueryConnectionsRequest {
            pagination: request.pagination.map(|pagination| pagination.into()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryClientConnectionsRequest {
    pub client_id: ClientId,
}

impl From<QueryClientConnectionsRequest> for RawQueryClientConnectionsRequest {
    fn from(request: QueryClientConnectionsRequest) -> Self {
        RawQueryClientConnectionsRequest {
            client_id: request.client_id.to_string(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryConnectionRequest {
    pub connection_id: ConnectionId,
    pub height: QueryHeight,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryConnectionChannelsRequest {
    pub connection_id: ConnectionId,
    pub pagination: Option<PageRequest>,
}

impl From<QueryConnectionChannelsRequest> for RawQueryConnectionChannelsRequest {
    fn from(request: QueryConnectionChannelsRequest) -> Self {
        RawQueryConnectionChannelsRequest {
            connection: request.connection_id.to_string(),
            pagination: request.pagination.map(|pagination| pagination.into()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryChannelsRequest {
    pub pagination: Option<PageRequest>,
}

impl From<QueryChannelsRequest> for RawQueryChannelsRequest {
    fn from(request: QueryChannelsRequest) -> Self {
        RawQueryChannelsRequest {
            pagination: request.pagination.map(|pagination| pagination.into()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryChannelRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub height: QueryHeight,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryChannelClientStateRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
}

impl From<QueryChannelClientStateRequest> for RawQueryChannelClientStateRequest {
    fn from(request: QueryChannelClientStateRequest) -> Self {
        RawQueryChannelClientStateRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryPacketCommitmentRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
    pub height: QueryHeight,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryPacketCommitmentsRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub pagination: Option<PageRequest>,
}

impl From<QueryPacketCommitmentsRequest> for RawQueryPacketCommitmentsRequest {
    fn from(request: QueryPacketCommitmentsRequest) -> Self {
        RawQueryPacketCommitmentsRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
            pagination: request.pagination.map(|pagination| pagination.into()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryPacketReceiptRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
    pub height: QueryHeight,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryUnreceivedPacketsRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub packet_commitment_sequences: Vec<Sequence>,
}

impl From<QueryUnreceivedPacketsRequest> for RawQueryUnreceivedPacketsRequest {
    fn from(request: QueryUnreceivedPacketsRequest) -> Self {
        RawQueryUnreceivedPacketsRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
            packet_commitment_sequences: request
                .packet_commitment_sequences
                .into_iter()
                .map(|seq| seq.into())
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryPacketAcknowledgementRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
    pub height: QueryHeight,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryPacketAcknowledgementsRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub pagination: Option<PageRequest>,
    pub packet_commitment_sequences: Vec<Sequence>,
}

impl From<QueryPacketAcknowledgementsRequest> for RawQueryPacketAcknowledgementsRequest {
    fn from(request: QueryPacketAcknowledgementsRequest) -> Self {
        RawQueryPacketAcknowledgementsRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
            pagination: request.pagination.map(|pagination| pagination.into()),
            packet_commitment_sequences: request
                .packet_commitment_sequences
                .into_iter()
                .map(|seq| seq.into())
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryUnreceivedAcksRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub packet_ack_sequences: Vec<Sequence>,
}

impl From<QueryUnreceivedAcksRequest> for RawQueryUnreceivedAcksRequest {
    fn from(request: QueryUnreceivedAcksRequest) -> Self {
        RawQueryUnreceivedAcksRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
            packet_ack_sequences: request
                .packet_ack_sequences
                .into_iter()
                .map(|seq| seq.into())
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryNextSequenceReceiveRequest {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub height: QueryHeight,
}

impl From<QueryNextSequenceReceiveRequest> for RawQueryNextSequenceReceiveRequest {
    fn from(request: QueryNextSequenceReceiveRequest) -> Self {
        RawQueryNextSequenceReceiveRequest {
            port_id: request.port_id.to_string(),
            channel_id: request.channel_id.to_string(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueryHostConsensusStateRequest {
    pub height: QueryHeight,
}

/// Used for queries and not yet standardized in channel's query.proto
#[derive(Clone, Debug)]
pub enum QueryTxRequest {
    Client(QueryClientEventRequest),
    Transaction(QueryTxHash),
}

#[derive(Clone, Debug)]
pub struct QueryTxHash(pub TxHash);

/// Used to query packet events:
/// - for events of type `event_id`,
/// - for a specific channel
/// - with sequences in `sequences`
/// - that occurred at a height either smaller or equal to `height` or exactly at `height`,
///   as specified by `event_height_qualifier`
#[derive(Clone, Debug)]
pub struct QueryPacketEventDataRequest {
    pub event_id: WithBlockDataType,
    pub source_channel_id: ChannelId,
    pub source_port_id: PortId,
    pub destination_channel_id: ChannelId,
    pub destination_port_id: PortId,
    pub sequences: Vec<Sequence>,
    pub height: Qualified<QueryHeight>,
}

/// Refines an inner type by assigning it to refer to either a:
///     - range of values (when using variant `SmallerEqual`), or
///     - to a specific value (with variant `Equal`).
///
/// For example, the inner type is typically a [`QueryHeight`].
/// In this case, we can capture and handle the two separate cases
/// that can appear when we want to query for packet event data,
/// depending on the request: The request might refer to a specific
/// height (i.e., we want packets from a block _at height_ T), or to
/// a range of heights (i.e., all packets _up to height_ T).
#[derive(Clone, Copy, Debug)]
pub enum Qualified<T> {
    SmallerEqual(T),
    Equal(T),
}

impl<T> Qualified<T> {
    /// Access the inner type.
    pub fn get(self) -> T {
        match self {
            Qualified::SmallerEqual(t) => t,
            Qualified::Equal(t) => t,
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Qualified<U> {
        match self {
            Qualified::SmallerEqual(t) => Qualified::SmallerEqual(f(t)),
            Qualified::Equal(t) => Qualified::Equal(f(t)),
        }
    }
}

impl<T: Display> Display for Qualified<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Qualified::SmallerEqual(a) => write!(f, "<={a}"),
            Qualified::Equal(a) => write!(f, "=={a}"),
        }
    }
}

/// Query request for a single client event, identified by `event_id`, for `client_id`.
#[derive(Clone, Debug)]
pub struct QueryClientEventRequest {
    pub query_height: QueryHeight,
    pub event_id: WithBlockDataType,
    pub client_id: ClientId,
    pub consensus_height: Height,
}

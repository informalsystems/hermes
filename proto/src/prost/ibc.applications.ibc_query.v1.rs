/// CrossChainQuery
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CrossChainQuery {
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub path: ::prost::alloc::string::String,
    #[prost(message, optional, tag="3")]
    pub local_timeout_height: ::core::option::Option<super::super::super::core::client::v1::Height>,
    #[prost(uint64, tag="4")]
    pub local_timeout_timestamp: u64,
    #[prost(uint64, tag="5")]
    pub query_height: u64,
    #[prost(string, tag="6")]
    pub client_id: ::prost::alloc::string::String,
}
/// CrossChainQueryResult
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CrossChainQueryResult {
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
    #[prost(enumeration="QueryResult", tag="2")]
    pub result: i32,
    #[prost(bytes="vec", tag="3")]
    pub data: ::prost::alloc::vec::Vec<u8>,
}
/// QueryResult
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum QueryResult {
    /// UNSPECIFIED
    Unspecified = 0,
    /// SUCCESS
    Success = 1,
    /// FAILURE
    Failure = 2,
    /// TIMEOUT
    Timeout = 3,
}
impl QueryResult {
    /// String value of the enum field names used in the ProtoBuf definition.
    ///
    /// The values are not transformed in any way and thus are considered stable
    /// (if the ProtoBuf definition does not change) and safe for programmatic use.
    pub fn as_str_name(&self) -> &'static str {
        match self {
            QueryResult::Unspecified => "QUERY_RESULT_UNSPECIFIED",
            QueryResult::Success => "QUERY_RESULT_SUCCESS",
            QueryResult::Failure => "QUERY_RESULT_FAILURE",
            QueryResult::Timeout => "QUERY_RESULT_TIMEOUT",
        }
    }
}
/// MsgSubmitCrossChainQuery
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSubmitCrossChainQuery {
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub path: ::prost::alloc::string::String,
    #[prost(message, optional, tag="3")]
    pub local_timeout_height: ::core::option::Option<super::super::super::core::client::v1::Height>,
    #[prost(uint64, tag="4")]
    pub local_timeout_stamp: u64,
    #[prost(uint64, tag="5")]
    pub query_height: u64,
    #[prost(string, tag="6")]
    pub client_id: ::prost::alloc::string::String,
    /// sender address
    #[prost(string, tag="7")]
    pub sender: ::prost::alloc::string::String,
    #[prost(string, tag="8")]
    pub source_port: ::prost::alloc::string::String,
    #[prost(string, tag="9")]
    pub source_channel: ::prost::alloc::string::String,
}
/// MsgSubmitCrossChainQueryResponse
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSubmitCrossChainQueryResponse {
    #[prost(string, tag="1")]
    pub query_id: ::prost::alloc::string::String,
    #[prost(uint64, tag="2")]
    pub cap_key: u64,
}
/// MsgSubmitCrossChainQueryResult
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSubmitCrossChainQueryResult {
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub path: ::prost::alloc::string::String,
    #[prost(uint64, tag="3")]
    pub query_height: u64,
    #[prost(enumeration="QueryResult", tag="4")]
    pub result: i32,
    #[prost(bytes="vec", tag="5")]
    pub data: ::prost::alloc::vec::Vec<u8>,
    #[prost(string, tag="6")]
    pub sender: ::prost::alloc::string::String,
    /// TODO: Proof specifications used in verifying counterparty state
    #[prost(message, repeated, tag="7")]
    pub proof_specs: ::prost::alloc::vec::Vec<super::super::super::super::ics23::ProofSpec>,
}
/// MsgSubmitCrossChainQueryResultResponse
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSubmitCrossChainQueryResultResponse {
}
/// IBCQueryPacketData defines a struct for the cross chain query packet payload
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct IbcQueryPacketData {
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub path: ::prost::alloc::string::String,
    #[prost(uint64, tag="3")]
    pub query_height: u64,
}
/// QueryCrossChainQuery
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCrossChainQueryResult {
    /// query id
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
}
/// QueryCrossChainQueryResponse
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCrossChainQueryResultResponse {
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
    #[prost(enumeration="QueryResult", tag="2")]
    pub result: i32,
    #[prost(bytes="vec", tag="3")]
    pub data: ::prost::alloc::vec::Vec<u8>,
}
/// EventQuerySubmitted emitted when process MsgSubmitCrossChainQuery tx
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct EventQuerySubmitted {
    #[prost(string, tag="1")]
    pub id: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub path: ::prost::alloc::string::String,
    #[prost(message, optional, tag="3")]
    pub local_timeout_height: ::core::option::Option<super::super::super::core::client::v1::Height>,
    #[prost(uint64, tag="4")]
    pub local_timeout_stamp: u64,
    #[prost(uint64, tag="5")]
    pub query_height: u64,
}
/// GenesisState defines the ICS31 ibc-query genesis state
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GenesisState {
    #[prost(message, repeated, tag="1")]
    pub queries: ::prost::alloc::vec::Vec<CrossChainQuery>,
    #[prost(message, repeated, tag="2")]
    pub results: ::prost::alloc::vec::Vec<CrossChainQueryResult>,
    #[prost(string, tag="3")]
    pub port_id: ::prost::alloc::string::String,
}

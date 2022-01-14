/// QueryAppVersionRequest is the request type for the Query/AppVersion RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryAppVersionRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// connection unique identifier
    #[prost(string, tag = "2")]
    pub connection_id: ::prost::alloc::string::String,
    /// whether the channel is ordered or unordered
    #[prost(enumeration = "super::super::channel::v1::Order", tag = "3")]
    pub ordering: i32,
    /// counterparty channel end
    #[prost(message, optional, tag = "4")]
    pub counterparty: ::core::option::Option<super::super::channel::v1::Counterparty>,
    /// proposed version
    #[prost(string, tag = "5")]
    pub proposed_version: ::prost::alloc::string::String,
}
/// QueryAppVersionResponse is the response type for the Query/AppVersion RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryAppVersionResponse {
    /// port id associated with the request identifiers
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// supported app version
    #[prost(string, tag = "2")]
    pub version: ::prost::alloc::string::String,
}

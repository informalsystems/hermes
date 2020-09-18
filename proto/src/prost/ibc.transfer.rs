/// MsgTransfer defines a msg to transfer fungible tokens (i.e Coins) between
/// ICS20 enabled chains. See ICS Spec here:
/// https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer#data-structures
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTransfer {
    /// the port on which the packet will be sent
    #[prost(string, tag="1")]
    pub source_port: std::string::String,
    /// the channel by which the packet will be sent
    #[prost(string, tag="2")]
    pub source_channel: std::string::String,
    /// the tokens to be transferred
    #[prost(message, optional, tag="3")]
    pub token: ::std::option::Option<super::super::cosmos::base::v1beta1::Coin>,
    /// the sender address
    #[prost(bytes, tag="4")]
    pub sender: std::vec::Vec<u8>,
    /// the recipient address on the destination chain
    #[prost(string, tag="5")]
    pub receiver: std::string::String,
    /// Timeout height relative to the current block height.
    /// The timeout is disabled when set to 0.
    #[prost(message, optional, tag="6")]
    pub timeout_height: ::std::option::Option<super::client::Height>,
    /// Timeout timestamp (in nanoseconds) relative to the current block timestamp.
    /// The timeout is disabled when set to 0.
    #[prost(uint64, tag="7")]
    pub timeout_timestamp: u64,
}
/// FungibleTokenPacketData defines a struct for the packet payload
/// See FungibleTokenPacketData spec:
/// https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer#data-structures
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct FungibleTokenPacketData {
    /// the token denomination to be transferred
    #[prost(string, tag="1")]
    pub denom: std::string::String,
    /// the token amount to be transferred
    #[prost(uint64, tag="2")]
    pub amount: u64,
    /// the sender address
    #[prost(string, tag="3")]
    pub sender: std::string::String,
    /// the recipient address on the destination chain
    #[prost(string, tag="4")]
    pub receiver: std::string::String,
}
/// FungibleTokenPacketAcknowledgement contains a boolean success flag and an
/// optional error msg error msg is empty string on success See spec for
/// onAcknowledgePacket:
/// https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer#packet-relay
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct FungibleTokenPacketAcknowledgement {
    #[prost(bool, tag="1")]
    pub success: bool,
    #[prost(string, tag="2")]
    pub error: std::string::String,
}
/// DenomTrace contains the base denomination for ICS20 fungible tokens and the source tracing
/// information path.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct DenomTrace {
    /// path defines the chain of port/channel identifiers used for tracing the source of the fungible
    /// token.
    #[prost(string, tag="1")]
    pub path: std::string::String,
    /// base denomination of the relayed fungible token.
    #[prost(string, tag="2")]
    pub base_denom: std::string::String,
}
/// Params defines the set of IBC transfer parameters.
/// NOTE: To prevent a single token from being transferred, set the TransfersEnabled parameter to
/// true and then set the bank module's SendEnabled parameter for the denomination to false.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Params {
    /// send_enabled enables or disables all cross-chain token transfers from this chain.
    #[prost(bool, tag="1")]
    pub send_enabled: bool,
    /// receive_enabled enables or disables all cross-chain token transfers to this chain.
    #[prost(bool, tag="2")]
    pub receive_enabled: bool,
}
/// QueryDenomTraceRequest is the request type for the Query/DenomTrace RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryDenomTraceRequest {
    /// hash (in hex format) of the denomination trace information.
    #[prost(string, tag="1")]
    pub hash: std::string::String,
}
/// QueryDenomTraceResponse is the response type for the Query/DenomTrace RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryDenomTraceResponse {
    /// denom_trace returns the requested denomination trace information.
    #[prost(message, optional, tag="1")]
    pub denom_trace: ::std::option::Option<DenomTrace>,
}
/// QueryConnectionsRequest is the request type for the Query/DenomTraces RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryDenomTracesRequest {
    /// pagination defines an optional pagination for the request.
    #[prost(message, optional, tag="1")]
    pub pagination: ::std::option::Option<super::super::cosmos::base::query::v1beta1::PageRequest>,
}
/// QueryConnectionsResponse is the response type for the Query/DenomTraces RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryDenomTracesResponse {
    /// denom_traces returns all denominations trace information.
    #[prost(message, repeated, tag="1")]
    pub denom_traces: ::std::vec::Vec<DenomTrace>,
    /// pagination defines the pagination in the response.
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::cosmos::base::query::v1beta1::PageResponse>,
}
/// QueryParamsRequest is the request type for the Query/Params RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryParamsRequest {
}
/// QueryParamsResponse is the response type for the Query/Params RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryParamsResponse {
    /// params defines the parameters of the module.
    #[prost(message, optional, tag="1")]
    pub params: ::std::option::Option<Params>,
}
/// GenesisState defines the ibc-transfer genesis state
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GenesisState {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(message, repeated, tag="2")]
    pub denom_traces: ::std::vec::Vec<DenomTrace>,
    #[prost(message, optional, tag="3")]
    pub params: ::std::option::Option<Params>,
}

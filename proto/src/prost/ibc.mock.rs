#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    #[prost(message, optional, tag="1")]
    pub height: ::core::option::Option<super::core::client::v1::Height>,
    #[prost(uint64, tag="2")]
    pub timestamp: u64,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    #[prost(message, optional, tag="1")]
    pub header: ::core::option::Option<Header>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusState {
    #[prost(message, optional, tag="1")]
    pub header: ::core::option::Option<Header>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Misbehaviour {
    #[prost(string, tag="1")]
    pub client_id: ::prost::alloc::string::String,
    #[prost(message, optional, tag="2")]
    pub header1: ::core::option::Option<Header>,
    #[prost(message, optional, tag="3")]
    pub header2: ::core::option::Option<Header>,
}

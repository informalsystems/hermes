/// ClientState defines a loopback (localhost) client. It requires (read-only)
/// access to keys outside the client prefix.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    /// self chain ID
    #[prost(string, tag = "1")]
    pub chain_id: ::prost::alloc::string::String,
    /// self latest block height
    #[prost(message, optional, tag = "2")]
    pub height: ::core::option::Option<super::super::super::core::client::v1::Height>,
}

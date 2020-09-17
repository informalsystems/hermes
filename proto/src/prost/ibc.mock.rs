#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    #[prost(message, optional, tag="1")]
    pub height: ::std::option::Option<super::client::Height>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    #[prost(message, optional, tag="1")]
    pub header: ::std::option::Option<Header>,
}

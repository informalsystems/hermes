/// GenesisState defines the ibc module's genesis state.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GenesisState {
    /// ICS002 - Clients genesis state
    #[prost(message, optional, tag="1")]
    pub client_genesis: ::std::option::Option<super::client::GenesisState>,
    /// ICS003 - Connections genesis state
    #[prost(message, optional, tag="2")]
    pub connection_genesis: ::std::option::Option<super::connection::GenesisState>,
    /// ICS004 - Channel genesis state
    #[prost(message, optional, tag="3")]
    pub channel_genesis: ::std::option::Option<super::channel::GenesisState>,
}

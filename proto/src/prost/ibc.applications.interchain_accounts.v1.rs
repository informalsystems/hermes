/// An InterchainAccount is defined as a BaseAccount & the address of the account owner on the controller chain
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct InterchainAccount {
    #[prost(message, optional, tag="1")]
    pub base_account: ::core::option::Option<super::super::super::super::cosmos::auth::v1beta1::BaseAccount>,
    #[prost(string, tag="2")]
    pub account_owner: ::prost::alloc::string::String,
}
/// InterchainAccountPacketData is comprised of a raw transaction, type of transaction and optional memo field.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct InterchainAccountPacketData {
    #[prost(enumeration="Type", tag="1")]
    pub r#type: i32,
    #[prost(bytes="vec", tag="2")]
    pub data: ::prost::alloc::vec::Vec<u8>,
    #[prost(string, tag="3")]
    pub memo: ::prost::alloc::string::String,
}
/// CosmosTx contains a list of sdk.Msg's. It should be used when sending transactions to an SDK host chain.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CosmosTx {
    #[prost(message, repeated, tag="1")]
    pub messages: ::prost::alloc::vec::Vec<super::super::super::super::google::protobuf::Any>,
}
/// Type defines a classification of message issued from a controller chain to its associated interchain accounts
/// host
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum Type {
    /// Default zero value enumeration
    Unspecified = 0,
    /// Execute a transaction on an interchain accounts host chain
    ExecuteTx = 1,
}
/// GenesisState defines the interchain accounts genesis state
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GenesisState {
    #[prost(message, optional, tag="1")]
    pub controller_genesis_state: ::core::option::Option<ControllerGenesisState>,
    #[prost(message, optional, tag="2")]
    pub host_genesis_state: ::core::option::Option<HostGenesisState>,
}
/// ControllerGenesisState defines the interchain accounts controller genesis state
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ControllerGenesisState {
    #[prost(message, repeated, tag="1")]
    pub active_channels: ::prost::alloc::vec::Vec<ActiveChannel>,
    #[prost(message, repeated, tag="2")]
    pub interchain_accounts: ::prost::alloc::vec::Vec<RegisteredInterchainAccount>,
    #[prost(string, repeated, tag="3")]
    pub ports: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
    #[prost(message, optional, tag="4")]
    pub params: ::core::option::Option<super::controller::v1::Params>,
}
/// HostGenesisState defines the interchain accounts host genesis state
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HostGenesisState {
    #[prost(message, repeated, tag="1")]
    pub active_channels: ::prost::alloc::vec::Vec<ActiveChannel>,
    #[prost(message, repeated, tag="2")]
    pub interchain_accounts: ::prost::alloc::vec::Vec<RegisteredInterchainAccount>,
    #[prost(string, tag="3")]
    pub port: ::prost::alloc::string::String,
    #[prost(message, optional, tag="4")]
    pub params: ::core::option::Option<super::host::v1::Params>,
}
/// ActiveChannel contains a connection ID, port ID and associated active channel ID
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ActiveChannel {
    #[prost(string, tag="1")]
    pub connection_id: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag="3")]
    pub channel_id: ::prost::alloc::string::String,
}
/// RegisteredInterchainAccount contains a connection ID, port ID and associated interchain account address
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct RegisteredInterchainAccount {
    #[prost(string, tag="1")]
    pub connection_id: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag="3")]
    pub account_address: ::prost::alloc::string::String,
}

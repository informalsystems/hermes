/// IdentifiedClientState defines a client state with additional client
/// identifier field.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct IdentifiedClientState {
    /// client identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    /// client state
    #[prost(message, optional, tag="2")]
    pub client_state: ::std::option::Option<::prost_types::Any>,
}
/// ClientConsensusStates defines all the stored consensus states for a given
/// client.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientConsensusStates {
    /// client identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    /// consensus states associated with the client
    #[prost(message, repeated, tag="2")]
    pub consensus_states: ::std::vec::Vec<::prost_types::Any>,
}
/// MsgCreateClient defines a message to create an IBC client
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgCreateClient {
    /// client unique identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    /// light client state
    #[prost(message, optional, tag="2")]
    pub client_state: ::std::option::Option<::prost_types::Any>,
    /// consensus state associated with the client that corresponds to a given
    /// height.
    #[prost(message, optional, tag="3")]
    pub consensus_state: ::std::option::Option<::prost_types::Any>,
    /// signer address
    #[prost(bytes, tag="4")]
    pub signer: std::vec::Vec<u8>,
}
/// MsgUpdateClient defines an sdk.Msg to update a IBC client state using
/// the given header.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgUpdateClient {
    /// client unique identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    /// header to update the light client
    #[prost(message, optional, tag="2")]
    pub header: ::std::option::Option<::prost_types::Any>,
    /// signer address
    #[prost(bytes, tag="3")]
    pub signer: std::vec::Vec<u8>,
}
/// MsgSubmitMisbehaviour defines an sdk.Msg type that submits Evidence for
/// light client misbehaviour.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSubmitMisbehaviour {
    /// client unique identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    /// misbehaviour used for freezing the light client
    #[prost(message, optional, tag="2")]
    pub misbehaviour: ::std::option::Option<::prost_types::Any>,
    /// signer address
    #[prost(bytes, tag="3")]
    pub signer: std::vec::Vec<u8>,
}
/// Height is a monotonically increasing data type
/// that can be compared against another Height for the purposes of updating and
/// freezing clients
///
/// Normally the EpochHeight is incremented at each height while keeping epoch
/// number the same However some consensus algorithms may choose to reset the
/// height in certain conditions e.g. hard forks, state-machine breaking changes
/// In these cases, the epoch number is incremented so that height continues to
/// be monitonically increasing even as the EpochHeight gets reset
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Height {
    /// the epoch that the client is currently on
    #[prost(uint64, tag="1")]
    pub epoch_number: u64,
    /// the height within the given epoch
    #[prost(uint64, tag="2")]
    pub epoch_height: u64,
}
/// GenesisState defines the ibc client submodule's genesis state.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GenesisState {
    /// client states with their corresponding identifiers
    #[prost(message, repeated, tag="1")]
    pub clients: ::std::vec::Vec<IdentifiedClientState>,
    /// consensus states from each client
    #[prost(message, repeated, tag="2")]
    pub clients_consensus: ::std::vec::Vec<ClientConsensusStates>,
    /// create localhost on initialization
    #[prost(bool, tag="3")]
    pub create_localhost: bool,
}
/// QueryClientStateRequest is the request type for the Query/ClientState RPC
/// method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryClientStateRequest {
    /// client state unique identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
}
/// QueryClientStateResponse is the response type for the Query/ClientState RPC
/// method. Besides the client state, it includes a proof and the height from
/// which the proof was retrieved.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryClientStateResponse {
    /// client state associated with the request identifier
    #[prost(message, optional, tag="1")]
    pub client_state: ::std::option::Option<::prost_types::Any>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="3")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<Height>,
}
/// QueryClientStatesRequest is the request type for the Query/ClientStates RPC
/// method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryClientStatesRequest {
    /// pagination request
    #[prost(message, optional, tag="1")]
    pub pagination: ::std::option::Option<super::super::cosmos::base::query::v1beta1::PageRequest>,
}
/// QueryClientStatesResponse is the response type for the Query/ClientStates RPC
/// method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryClientStatesResponse {
    /// list of stored ClientStates of the chain.
    #[prost(message, repeated, tag="1")]
    pub client_states: ::std::vec::Vec<IdentifiedClientState>,
    /// pagination response
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::cosmos::base::query::v1beta1::PageResponse>,
}
/// QueryConsensusStateRequest is the request type for the Query/ConsensusState RPC method. Besides
/// the consensus state, it includes a proof and the height from which the proof was retrieved.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConsensusStateRequest {
    /// client identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    /// consensus state epoch number 
    #[prost(uint64, tag="2")]
    pub epoch_number: u64,
    /// consensus state epoch height
    #[prost(uint64, tag="3")]
    pub epoch_height: u64,
    /// latest_height overrrides the height field and queries the latest stored ConsensusState
    #[prost(bool, tag="4")]
    pub latest_height: bool,
}
/// QueryConsensusStateResponse is the response type for the Query/ConsensusState RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConsensusStateResponse {
    /// consensus state associated with the client identifier at the given height
    #[prost(message, optional, tag="1")]
    pub consensus_state: ::std::option::Option<::prost_types::Any>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="3")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<Height>,
}
/// QueryConsensusStatesRequest is the request type for the Query/ConsensusStates RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConsensusStatesRequest {
    /// client identifier
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    /// pagination request
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::cosmos::base::query::v1beta1::PageRequest>,
}
/// QueryConsensusStatesResponse is the response type for the Query/ConsensusStates RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConsensusStatesResponse {
    /// consensus states associated with the identifier
    #[prost(message, repeated, tag="1")]
    pub consensus_states: ::std::vec::Vec<::prost_types::Any>,
    /// pagination response
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::cosmos::base::query::v1beta1::PageResponse>,
}

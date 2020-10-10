/// ClientState defines a solo machine client that tracks the current consensus
/// state and if the client is frozen.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    /// latest sequence of the client state
    #[prost(uint64, tag="1")]
    pub sequence: u64,
    /// frozen sequence of the solo machine
    #[prost(uint64, tag="2")]
    pub frozen_sequence: u64,
    #[prost(message, optional, tag="3")]
    pub consensus_state: ::std::option::Option<ConsensusState>,
    /// when set to true, will allow governance to update a solo machine client.
    /// The client will be unfrozen if it is frozen.
    #[prost(bool, tag="4")]
    pub allow_update_after_proposal: bool,
}
/// ConsensusState defines a solo machine consensus state. The sequence of a consensus state
/// is contained in the "height" key used in storing the consensus state.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusState {
    /// public key of the solo machine
    #[prost(message, optional, tag="1")]
    pub public_key: ::std::option::Option<::prost_types::Any>,
    /// diversifier allows the same public key to be re-used across different solo machine clients
    /// (potentially on different chains) without being considered misbehaviour.
    #[prost(string, tag="2")]
    pub diversifier: std::string::String,
    #[prost(uint64, tag="3")]
    pub timestamp: u64,
}
/// Header defines a solo machine consensus header
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    /// sequence to update solo machine public key at
    #[prost(uint64, tag="1")]
    pub sequence: u64,
    #[prost(uint64, tag="2")]
    pub timestamp: u64,
    #[prost(bytes, tag="3")]
    pub signature: std::vec::Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub new_public_key: ::std::option::Option<::prost_types::Any>,
    #[prost(string, tag="5")]
    pub new_diversifier: std::string::String,
}
/// Misbehaviour defines misbehaviour for a solo machine which consists
/// of a sequence and two signatures over different messages at that sequence.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Misbehaviour {
    #[prost(string, tag="1")]
    pub client_id: std::string::String,
    #[prost(uint64, tag="2")]
    pub sequence: u64,
    #[prost(message, optional, tag="3")]
    pub signature_one: ::std::option::Option<SignatureAndData>,
    #[prost(message, optional, tag="4")]
    pub signature_two: ::std::option::Option<SignatureAndData>,
}
/// SignatureAndData contains a signature and the data signed over to create that
/// signature.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignatureAndData {
    #[prost(bytes, tag="1")]
    pub signature: std::vec::Vec<u8>,
    #[prost(bytes, tag="2")]
    pub data: std::vec::Vec<u8>,
}
/// TimestampedSignature contains the signature and the timestamp of the
/// signature.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TimestampedSignature {
    #[prost(bytes, tag="1")]
    pub signature: std::vec::Vec<u8>,
    #[prost(uint64, tag="2")]
    pub timestamp: u64,
}
/// SignBytes defines the signed bytes used for signature verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignBytes {
    #[prost(uint64, tag="1")]
    pub sequence: u64,
    #[prost(uint64, tag="2")]
    pub timestamp: u64,
    #[prost(string, tag="3")]
    pub diversifier: std::string::String,
    /// marshaled data
    #[prost(bytes, tag="4")]
    pub data: std::vec::Vec<u8>,
}
/// HeaderData returns the SignBytes data for misbehaviour verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HeaderData {
    /// header public key
    #[prost(message, optional, tag="1")]
    pub new_pub_key: ::std::option::Option<::prost_types::Any>,
    /// header diversifier
    #[prost(string, tag="2")]
    pub new_diversifier: std::string::String,
}
/// ClientStateData returns the SignBytes data for client state verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientStateData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
    #[prost(message, optional, tag="2")]
    pub client_state: ::std::option::Option<::prost_types::Any>,
}
/// ConsensusStateSignBytes returns the SignBytes data for consensus state
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusStateData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
    #[prost(message, optional, tag="2")]
    pub consensus_state: ::std::option::Option<::prost_types::Any>,
}
/// ConnectionStateSignBytes returns the SignBytes data for connection state
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConnectionStateData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
    #[prost(message, optional, tag="2")]
    pub connection: ::std::option::Option<super::super::super::connection::ConnectionEnd>,
}
/// ChannelStateSignBytes returns the SignBytes data for channel state
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ChannelStateData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
    #[prost(message, optional, tag="2")]
    pub channel: ::std::option::Option<super::super::super::channel::Channel>,
}
/// PacketCommitmentSignBytes returns the SignBytes data for packet commitment
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketCommitmentData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
    #[prost(bytes, tag="2")]
    pub commitment: std::vec::Vec<u8>,
}
/// PacketAcknowledgementSignBytes returns the SignBytes data for acknowledgement
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketAcknowledgementData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
    #[prost(bytes, tag="2")]
    pub acknowledgement: std::vec::Vec<u8>,
}
/// PacketAcknowledgementAbsenceSignBytes returns the SignBytes data for
/// acknowledgement absence verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketAcknowledgementAbsenseData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
}
/// NextSequenceRecv returns the SignBytes data for verification of the next
/// sequence to be received.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct NextSequenceRecvData {
    #[prost(bytes, tag="1")]
    pub path: std::vec::Vec<u8>,
    #[prost(uint64, tag="2")]
    pub next_seq_recv: u64,
}

/// ClientState defines a solo machine client that tracks the current consensus
/// state and if the client is frozen.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    /// frozen sequence of the solo machine
    #[prost(uint64, tag="1")]
    pub frozen_sequence: u64,
    #[prost(message, optional, tag="2")]
    pub consensus_state: ::std::option::Option<ConsensusState>,
}
/// ConsensusState defines a solo machine consensus state
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusState {
    /// current sequence of the consensus state
    #[prost(uint64, tag="1")]
    pub sequence: u64,
    /// public key of the solo machine
    #[prost(message, optional, tag="2")]
    pub public_key: ::std::option::Option<super::super::super::super::cosmos::base::crypto::v1beta1::PublicKey>,
    #[prost(uint64, tag="3")]
    pub timestamp: u64,
}
/// Header defines a solo machine consensus header
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    /// sequence to update solo machine public key at
    #[prost(uint64, tag="1")]
    pub sequence: u64,
    #[prost(bytes, tag="2")]
    pub signature: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub new_public_key: ::std::option::Option<super::super::super::super::cosmos::base::crypto::v1beta1::PublicKey>,
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

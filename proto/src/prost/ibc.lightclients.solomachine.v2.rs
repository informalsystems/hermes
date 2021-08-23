/// ClientState defines a solo machine client that tracks the current consensus
/// state and if the client is frozen.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    /// latest sequence of the client state
    #[prost(uint64, tag = "1")]
    pub sequence: u64,
    /// frozen sequence of the solo machine
    #[prost(bool, tag = "2")]
    pub is_frozen: bool,
    #[prost(message, optional, tag = "3")]
    pub consensus_state: ::core::option::Option<ConsensusState>,
    /// when set to true, will allow governance to update a solo machine client.
    /// The client will be unfrozen if it is frozen.
    #[prost(bool, tag = "4")]
    pub allow_update_after_proposal: bool,
}
/// ConsensusState defines a solo machine consensus state. The sequence of a
/// consensus state is contained in the "height" key used in storing the
/// consensus state.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusState {
    /// public key of the solo machine
    #[prost(message, optional, tag = "1")]
    pub public_key: ::core::option::Option<::prost_types::Any>,
    /// diversifier allows the same public key to be re-used across different solo
    /// machine clients (potentially on different chains) without being considered
    /// misbehaviour.
    #[prost(string, tag = "2")]
    pub diversifier: ::prost::alloc::string::String,
    #[prost(uint64, tag = "3")]
    pub timestamp: u64,
}
/// Header defines a solo machine consensus header
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    /// sequence to update solo machine public key at
    #[prost(uint64, tag = "1")]
    pub sequence: u64,
    #[prost(uint64, tag = "2")]
    pub timestamp: u64,
    #[prost(bytes = "vec", tag = "3")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "4")]
    pub new_public_key: ::core::option::Option<::prost_types::Any>,
    #[prost(string, tag = "5")]
    pub new_diversifier: ::prost::alloc::string::String,
}
/// Misbehaviour defines misbehaviour for a solo machine which consists
/// of a sequence and two signatures over different messages at that sequence.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Misbehaviour {
    #[prost(string, tag = "1")]
    pub client_id: ::prost::alloc::string::String,
    #[prost(uint64, tag = "2")]
    pub sequence: u64,
    #[prost(message, optional, tag = "3")]
    pub signature_one: ::core::option::Option<SignatureAndData>,
    #[prost(message, optional, tag = "4")]
    pub signature_two: ::core::option::Option<SignatureAndData>,
}
/// SignatureAndData contains a signature and the data signed over to create that
/// signature.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignatureAndData {
    #[prost(bytes = "vec", tag = "1")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
    #[prost(enumeration = "DataType", tag = "2")]
    pub data_type: i32,
    #[prost(bytes = "vec", tag = "3")]
    pub data: ::prost::alloc::vec::Vec<u8>,
    #[prost(uint64, tag = "4")]
    pub timestamp: u64,
}
/// TimestampedSignatureData contains the signature data and the timestamp of the
/// signature.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TimestampedSignatureData {
    #[prost(bytes = "vec", tag = "1")]
    pub signature_data: ::prost::alloc::vec::Vec<u8>,
    #[prost(uint64, tag = "2")]
    pub timestamp: u64,
}
/// SignBytes defines the signed bytes used for signature verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignBytes {
    #[prost(uint64, tag = "1")]
    pub sequence: u64,
    #[prost(uint64, tag = "2")]
    pub timestamp: u64,
    #[prost(string, tag = "3")]
    pub diversifier: ::prost::alloc::string::String,
    /// type of the data used
    #[prost(enumeration = "DataType", tag = "4")]
    pub data_type: i32,
    /// marshaled data
    #[prost(bytes = "vec", tag = "5")]
    pub data: ::prost::alloc::vec::Vec<u8>,
}
/// HeaderData returns the SignBytes data for update verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HeaderData {
    /// header public key
    #[prost(message, optional, tag = "1")]
    pub new_pub_key: ::core::option::Option<::prost_types::Any>,
    /// header diversifier
    #[prost(string, tag = "2")]
    pub new_diversifier: ::prost::alloc::string::String,
}
/// ClientStateData returns the SignBytes data for client state verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientStateData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "2")]
    pub client_state: ::core::option::Option<::prost_types::Any>,
}
/// ConsensusStateData returns the SignBytes data for consensus state
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusStateData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "2")]
    pub consensus_state: ::core::option::Option<::prost_types::Any>,
}
/// ConnectionStateData returns the SignBytes data for connection state
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConnectionStateData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "2")]
    pub connection:
        ::core::option::Option<super::super::super::core::connection::v1::ConnectionEnd>,
}
/// ChannelStateData returns the SignBytes data for channel state
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ChannelStateData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "2")]
    pub channel: ::core::option::Option<super::super::super::core::channel::v1::Channel>,
}
/// PacketCommitmentData returns the SignBytes data for packet commitment
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketCommitmentData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "2")]
    pub commitment: ::prost::alloc::vec::Vec<u8>,
}
/// PacketAcknowledgementData returns the SignBytes data for acknowledgement
/// verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketAcknowledgementData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "2")]
    pub acknowledgement: ::prost::alloc::vec::Vec<u8>,
}
/// PacketReceiptAbsenceData returns the SignBytes data for
/// packet receipt absence verification.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketReceiptAbsenceData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
}
/// NextSequenceRecvData returns the SignBytes data for verification of the next
/// sequence to be received.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct NextSequenceRecvData {
    #[prost(bytes = "vec", tag = "1")]
    pub path: ::prost::alloc::vec::Vec<u8>,
    #[prost(uint64, tag = "2")]
    pub next_seq_recv: u64,
}
/// DataType defines the type of solo machine proof being created. This is done
/// to preserve uniqueness of different data sign byte encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum DataType {
    /// Default State
    UninitializedUnspecified = 0,
    /// Data type for client state verification
    ClientState = 1,
    /// Data type for consensus state verification
    ConsensusState = 2,
    /// Data type for connection state verification
    ConnectionState = 3,
    /// Data type for channel state verification
    ChannelState = 4,
    /// Data type for packet commitment verification
    PacketCommitment = 5,
    /// Data type for packet acknowledgement verification
    PacketAcknowledgement = 6,
    /// Data type for packet receipt absence verification
    PacketReceiptAbsence = 7,
    /// Data type for next sequence recv verification
    NextSequenceRecv = 8,
    /// Data type for header verification
    Header = 9,
}

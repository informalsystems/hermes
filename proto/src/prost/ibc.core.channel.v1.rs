/// MsgChannelOpenInit defines an sdk.Msg to initialize a channel handshake. It
/// is called by a relayer on Chain A.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenInit {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    #[prost(message, optional, tag="3")]
    pub channel: ::std::option::Option<Channel>,
    #[prost(string, tag="4")]
    pub signer: std::string::String,
}
/// MsgChannelOpenInit  defines a msg sent by a Relayer to try to open a channel
/// on Chain B.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenTry {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(string, tag="2")]
    pub desired_channel_id: std::string::String,
    #[prost(string, tag="3")]
    pub counterparty_chosen_channel_id: std::string::String,
    #[prost(message, optional, tag="4")]
    pub channel: ::std::option::Option<Channel>,
    #[prost(string, tag="5")]
    pub counterparty_version: std::string::String,
    #[prost(bytes, tag="6")]
    pub proof_init: std::vec::Vec<u8>,
    #[prost(message, optional, tag="7")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="8")]
    pub signer: std::string::String,
}
/// MsgChannelOpenAck defines a msg sent by a Relayer to Chain A to acknowledge
/// the change of channel state to TRYOPEN on Chain B.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenAck {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    #[prost(string, tag="3")]
    pub counterparty_channel_id: std::string::String,
    #[prost(string, tag="4")]
    pub counterparty_version: std::string::String,
    #[prost(bytes, tag="5")]
    pub proof_try: std::vec::Vec<u8>,
    #[prost(message, optional, tag="6")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="7")]
    pub signer: std::string::String,
}
/// MsgChannelOpenConfirm defines a msg sent by a Relayer to Chain B to
/// acknowledge the change of channel state to OPEN on Chain A.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenConfirm {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    #[prost(bytes, tag="3")]
    pub proof_ack: std::vec::Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="5")]
    pub signer: std::string::String,
}
/// MsgChannelCloseInit defines a msg sent by a Relayer to Chain A
/// to close a channel with Chain B.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseInit {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    #[prost(string, tag="3")]
    pub signer: std::string::String,
}
/// MsgChannelCloseConfirm defines a msg sent by a Relayer to Chain B
/// to acknowledge the change of channel state to CLOSED on Chain A.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseConfirm {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    #[prost(bytes, tag="3")]
    pub proof_init: std::vec::Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="5")]
    pub signer: std::string::String,
}
/// MsgRecvPacket receives incoming IBC packet
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgRecvPacket {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="4")]
    pub signer: std::string::String,
}
/// MsgTimeout receives timed-out packet
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeout {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(uint64, tag="4")]
    pub next_sequence_recv: u64,
    #[prost(string, tag="5")]
    pub signer: std::string::String,
}
/// MsgTimeoutOnClose timed-out packet upon counterparty channel closure.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeoutOnClose {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    #[prost(bytes, tag="3")]
    pub proof_close: std::vec::Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(uint64, tag="5")]
    pub next_sequence_recv: u64,
    #[prost(string, tag="6")]
    pub signer: std::string::String,
}
/// MsgAcknowledgement receives incoming IBC acknowledgement
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgAcknowledgement {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub acknowledgement: std::vec::Vec<u8>,
    #[prost(bytes, tag="3")]
    pub proof: std::vec::Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="5")]
    pub signer: std::string::String,
}
/// Channel defines pipeline for exactly-once packet delivery between specific
/// modules on separate blockchains, which has at least one end capable of
/// sending packets and one end capable of receiving packets.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Channel {
    /// current state of the channel end
    #[prost(enumeration="State", tag="1")]
    pub state: i32,
    /// whether the channel is ordered or unordered
    #[prost(enumeration="Order", tag="2")]
    pub ordering: i32,
    /// counterparty channel end
    #[prost(message, optional, tag="3")]
    pub counterparty: ::std::option::Option<Counterparty>,
    /// list of connection identifiers, in order, along which packets sent on
    /// this channel will travel
    #[prost(string, repeated, tag="4")]
    pub connection_hops: ::std::vec::Vec<std::string::String>,
    /// opaque channel version, which is agreed upon during the handshake
    #[prost(string, tag="5")]
    pub version: std::string::String,
}
/// IdentifiedChannel defines a channel with additional port and channel
/// identifier fields.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct IdentifiedChannel {
    /// current state of the channel end
    #[prost(enumeration="State", tag="1")]
    pub state: i32,
    /// whether the channel is ordered or unordered
    #[prost(enumeration="Order", tag="2")]
    pub ordering: i32,
    /// counterparty channel end
    #[prost(message, optional, tag="3")]
    pub counterparty: ::std::option::Option<Counterparty>,
    /// list of connection identifiers, in order, along which packets sent on
    /// this channel will travel
    #[prost(string, repeated, tag="4")]
    pub connection_hops: ::std::vec::Vec<std::string::String>,
    /// opaque channel version, which is agreed upon during the handshake
    #[prost(string, tag="5")]
    pub version: std::string::String,
    /// port identifier
    #[prost(string, tag="6")]
    pub port_id: std::string::String,
    /// channel identifier
    #[prost(string, tag="7")]
    pub channel_id: std::string::String,
}
/// Counterparty defines a channel end counterparty
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Counterparty {
    /// port on the counterparty chain which owns the other end of the channel.
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel end on the counterparty chain
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
}
/// Packet defines a type that carries data across different chains through IBC
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Packet {
    /// number corresponds to the order of sends and receives, where a Packet
    /// with an earlier sequence number must be sent and received before a Packet
    /// with a later sequence number.
    #[prost(uint64, tag="1")]
    pub sequence: u64,
    /// identifies the port on the sending chain.
    #[prost(string, tag="2")]
    pub source_port: std::string::String,
    /// identifies the channel end on the sending chain.
    #[prost(string, tag="3")]
    pub source_channel: std::string::String,
    /// identifies the port on the receiving chain.
    #[prost(string, tag="4")]
    pub destination_port: std::string::String,
    /// identifies the channel end on the receiving chain.
    #[prost(string, tag="5")]
    pub destination_channel: std::string::String,
    /// actual opaque bytes transferred directly to the application module
    #[prost(bytes, tag="6")]
    pub data: std::vec::Vec<u8>,
    /// block height after which the packet times out
    #[prost(message, optional, tag="7")]
    pub timeout_height: ::std::option::Option<super::super::client::v1::Height>,
    /// block timestamp (in nanoseconds) after which the packet times out
    #[prost(uint64, tag="8")]
    pub timeout_timestamp: u64,
}
/// PacketAckCommitment defines the genesis type necessary to retrieve and store
/// acknowlegements.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketAckCommitment {
    /// channel port identifier.
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier.
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// packet sequence.
    #[prost(uint64, tag="3")]
    pub sequence: u64,
    /// packet commitment hash.
    #[prost(bytes, tag="4")]
    pub hash: std::vec::Vec<u8>,
}
/// Acknowledgement is the recommended acknowledgement format to be used by
/// app-specific protocols.
/// NOTE: The field numbers 21 and 22 were explicitly chosen to avoid accidental
/// conflicts with other protobuf message formats used for acknowledgements.
/// The first byte of any message with this format will be the non-ASCII values
/// `0xaa` (result) or `0xb2` (error). Implemented as defined by ICS:
/// https://github.com/cosmos/ics/tree/master/spec/ics-004-channel-and-packet-semantics#acknowledgement-envelope
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Acknowledgement {
    /// response contains either a result or an error and must be non-empty
    #[prost(oneof="acknowledgement::Response", tags="21, 22")]
    pub response: ::std::option::Option<acknowledgement::Response>,
}
pub mod acknowledgement {
    /// response contains either a result or an error and must be non-empty
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Response {
        #[prost(bytes, tag="21")]
        Result(std::vec::Vec<u8>),
        #[prost(string, tag="22")]
        Error(std::string::String),
    }
}
/// State defines if a channel is in one of the following states:
/// CLOSED, INIT, TRYOPEN, OPEN or UNINITIALIZED.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum State {
    /// Default State
    UninitializedUnspecified = 0,
    /// A channel has just started the opening handshake.
    Init = 1,
    /// A channel has acknowledged the handshake step on the counterparty chain.
    Tryopen = 2,
    /// A channel has completed the handshake. Open channels are
    /// ready to send and receive packets.
    Open = 3,
    /// A channel has been closed and can no longer be used to send or receive
    /// packets.
    Closed = 4,
}
/// Order defines if a channel is ORDERED or UNORDERED
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum Order {
    /// zero-value for channel ordering
    NoneUnspecified = 0,
    /// packets can be delivered in any order, which may differ from the order in
    /// which they were sent.
    Unordered = 1,
    /// packets are delivered exactly in the order which they were sent
    Ordered = 2,
}
/// GenesisState defines the ibc channel submodule's genesis state.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GenesisState {
    #[prost(message, repeated, tag="1")]
    pub channels: ::std::vec::Vec<IdentifiedChannel>,
    #[prost(message, repeated, tag="2")]
    pub acknowledgements: ::std::vec::Vec<PacketAckCommitment>,
    #[prost(message, repeated, tag="3")]
    pub commitments: ::std::vec::Vec<PacketAckCommitment>,
    #[prost(message, repeated, tag="4")]
    pub send_sequences: ::std::vec::Vec<PacketSequence>,
    #[prost(message, repeated, tag="5")]
    pub recv_sequences: ::std::vec::Vec<PacketSequence>,
    #[prost(message, repeated, tag="6")]
    pub ack_sequences: ::std::vec::Vec<PacketSequence>,
}
/// PacketSequence defines the genesis type necessary to retrieve and store
/// next send and receive sequences.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketSequence {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    #[prost(uint64, tag="3")]
    pub sequence: u64,
}
/// QueryChannelRequest is the request type for the Query/Channel RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
}
/// QueryChannelResponse is the response type for the Query/Channel RPC method.
/// Besides the Channel end, it includes a proof and the height from which the
/// proof was retrieved.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelResponse {
    /// channel associated with the request identifiers
    #[prost(message, optional, tag="1")]
    pub channel: ::std::option::Option<Channel>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="3")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryChannelsRequest is the request type for the Query/Channels RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelsRequest {
    /// pagination request
    #[prost(message, optional, tag="1")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageRequest>,
}
/// QueryChannelsResponse is the response type for the Query/Channels RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelsResponse {
    /// list of stored channels of the chain.
    #[prost(message, repeated, tag="1")]
    pub channels: ::std::vec::Vec<IdentifiedChannel>,
    /// pagination response
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageResponse>,
    /// query block height
    #[prost(message, optional, tag="3")]
    pub height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryConnectionChannelsRequest is the request type for the
/// Query/QueryConnectionChannels RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConnectionChannelsRequest {
    /// connection unique identifier
    #[prost(string, tag="1")]
    pub connection: std::string::String,
    /// pagination request
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageRequest>,
}
/// QueryConnectionChannelsResponse is the Response type for the
/// Query/QueryConnectionChannels RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConnectionChannelsResponse {
    /// list of channels associated with a connection.
    #[prost(message, repeated, tag="1")]
    pub channels: ::std::vec::Vec<IdentifiedChannel>,
    /// pagination response
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageResponse>,
    /// query block height
    #[prost(message, optional, tag="3")]
    pub height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryChannelClientStateRequest is the request type for the Query/ClientState
/// RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelClientStateRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
}
/// QueryChannelClientStateResponse is the Response type for the
/// Query/QueryChannelClientState RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelClientStateResponse {
    /// client state associated with the channel
    #[prost(message, optional, tag="1")]
    pub identified_client_state: ::std::option::Option<super::super::client::v1::IdentifiedClientState>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="3")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryChannelConsensusStateRequest is the request type for the
/// Query/ConsensusState RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelConsensusStateRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// version number of the consensus state
    #[prost(uint64, tag="3")]
    pub version_number: u64,
    /// version height of the consensus state
    #[prost(uint64, tag="4")]
    pub version_height: u64,
}
/// QueryChannelClientStateResponse is the Response type for the
/// Query/QueryChannelClientState RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelConsensusStateResponse {
    /// consensus state associated with the channel
    #[prost(message, optional, tag="1")]
    pub consensus_state: ::std::option::Option<::prost_types::Any>,
    /// client ID associated with the consensus state
    #[prost(string, tag="2")]
    pub client_id: std::string::String,
    /// merkle proof of existence
    #[prost(bytes, tag="3")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="4")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="5")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketCommitmentRequest is the request type for the
/// Query/PacketCommitment RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// packet sequence
    #[prost(uint64, tag="3")]
    pub sequence: u64,
}
/// QueryPacketCommitmentResponse defines the client query response for a packet
/// which also includes a proof, its path and the height form which the proof was
/// retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentResponse {
    /// packet associated with the request fields
    #[prost(bytes, tag="1")]
    pub commitment: std::vec::Vec<u8>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="3")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketCommitmentsRequest is the request type for the
/// Query/QueryPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentsRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// pagination request
    #[prost(message, optional, tag="3")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageRequest>,
}
/// QueryPacketCommitmentsResponse is the request type for the
/// Query/QueryPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentsResponse {
    #[prost(message, repeated, tag="1")]
    pub commitments: ::std::vec::Vec<PacketAckCommitment>,
    /// pagination response
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageResponse>,
    /// query block height
    #[prost(message, optional, tag="3")]
    pub height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketAcknowledgementRequest is the request type for the
/// Query/PacketAcknowledgement RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// packet sequence
    #[prost(uint64, tag="3")]
    pub sequence: u64,
}
/// QueryPacketAcknowledgementResponse defines the client query response for a
/// packet which also includes a proof, its path and the height form which the
/// proof was retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementResponse {
    /// packet associated with the request fields
    #[prost(bytes, tag="1")]
    pub acknowledgement: std::vec::Vec<u8>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="3")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryUnreceivedPacketsRequest is the request type for the
/// Query/UnreceivedPackets RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedPacketsRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// list of packet sequences
    #[prost(uint64, repeated, tag="3")]
    pub packet_commitment_sequences: ::std::vec::Vec<u64>,
}
/// QueryUnreceivedPacketsResponse is the response type for the
/// Query/UnreceivedPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedPacketsResponse {
    /// list of unreceived packet sequences
    #[prost(uint64, repeated, tag="1")]
    pub sequences: ::std::vec::Vec<u64>,
    /// query block height
    #[prost(message, optional, tag="2")]
    pub height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryUnrelayedAcksRequest is the request type for the
/// Query/UnrelayedAcks RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnrelayedAcksRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// list of commitment sequences
    #[prost(uint64, repeated, tag="3")]
    pub packet_commitment_sequences: ::std::vec::Vec<u64>,
}
/// QueryUnrelayedAcksResponse is the response type for the
/// Query/UnrelayedAcks RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnrelayedAcksResponse {
    /// list of unrelayed acknowledgement sequences
    #[prost(uint64, repeated, tag="1")]
    pub sequences: ::std::vec::Vec<u64>,
    /// query block height
    #[prost(message, optional, tag="2")]
    pub height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryNextSequenceReceiveRequest is the request type for the
/// Query/QueryNextSequenceReceiveRequest RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryNextSequenceReceiveRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
}
/// QuerySequenceResponse is the request type for the
/// Query/QueryNextSequenceReceiveResponse RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryNextSequenceReceiveResponse {
    /// next sequence receive number
    #[prost(uint64, tag="1")]
    pub next_sequence_receive: u64,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// merkle proof path
    #[prost(string, tag="3")]
    pub proof_path: std::string::String,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}

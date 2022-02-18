/// Channel defines pipeline for exactly-once packet delivery between specific
/// modules on separate blockchains, which has at least one end capable of
/// sending packets and one end capable of receiving packets.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Channel {
    /// current state of the channel end
    #[prost(enumeration = "State", tag = "1")]
    pub state: i32,
    /// whether the channel is ordered or unordered
    #[prost(enumeration = "Order", tag = "2")]
    pub ordering: i32,
    /// counterparty channel end
    #[prost(message, optional, tag = "3")]
    pub counterparty: ::core::option::Option<Counterparty>,
    /// list of connection identifiers, in order, along which packets sent on
    /// this channel will travel
    #[prost(string, repeated, tag = "4")]
    pub connection_hops: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
    /// opaque channel version, which is agreed upon during the handshake
    #[prost(string, tag = "5")]
    pub version: ::prost::alloc::string::String,
}
/// IdentifiedChannel defines a channel with additional port and channel
/// identifier fields.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct IdentifiedChannel {
    /// current state of the channel end
    #[prost(enumeration = "State", tag = "1")]
    pub state: i32,
    /// whether the channel is ordered or unordered
    #[prost(enumeration = "Order", tag = "2")]
    pub ordering: i32,
    /// counterparty channel end
    #[prost(message, optional, tag = "3")]
    pub counterparty: ::core::option::Option<Counterparty>,
    /// list of connection identifiers, in order, along which packets sent on
    /// this channel will travel
    #[prost(string, repeated, tag = "4")]
    pub connection_hops: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
    /// opaque channel version, which is agreed upon during the handshake
    #[prost(string, tag = "5")]
    pub version: ::prost::alloc::string::String,
    /// port identifier
    #[prost(string, tag = "6")]
    pub port_id: ::prost::alloc::string::String,
    /// channel identifier
    #[prost(string, tag = "7")]
    pub channel_id: ::prost::alloc::string::String,
}
/// Counterparty defines a channel end counterparty
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Counterparty {
    /// port on the counterparty chain which owns the other end of the channel.
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel end on the counterparty chain
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
}
/// Packet defines a type that carries data across different chains through IBC
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Packet {
    /// number corresponds to the order of sends and receives, where a Packet
    /// with an earlier sequence number must be sent and received before a Packet
    /// with a later sequence number.
    #[prost(uint64, tag = "1")]
    pub sequence: u64,
    /// identifies the port on the sending chain.
    #[prost(string, tag = "2")]
    pub source_port: ::prost::alloc::string::String,
    /// identifies the channel end on the sending chain.
    #[prost(string, tag = "3")]
    pub source_channel: ::prost::alloc::string::String,
    /// identifies the port on the receiving chain.
    #[prost(string, tag = "4")]
    pub destination_port: ::prost::alloc::string::String,
    /// identifies the channel end on the receiving chain.
    #[prost(string, tag = "5")]
    pub destination_channel: ::prost::alloc::string::String,
    /// actual opaque bytes transferred directly to the application module
    #[prost(bytes = "vec", tag = "6")]
    pub data: ::prost::alloc::vec::Vec<u8>,
    /// block height after which the packet times out
    #[prost(message, optional, tag = "7")]
    pub timeout_height: ::core::option::Option<super::super::client::v1::Height>,
    /// block timestamp (in nanoseconds) after which the packet times out
    #[prost(uint64, tag = "8")]
    pub timeout_timestamp: u64,
}
/// PacketState defines the generic type necessary to retrieve and store
/// packet commitments, acknowledgements, and receipts.
/// Caller is responsible for knowing the context necessary to interpret this
/// state as a commitment, acknowledgement, or a receipt.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketState {
    /// channel port identifier.
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier.
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// packet sequence.
    #[prost(uint64, tag = "3")]
    pub sequence: u64,
    /// embedded data that represents packet state.
    #[prost(bytes = "vec", tag = "4")]
    pub data: ::prost::alloc::vec::Vec<u8>,
}
/// Acknowledgement is the recommended acknowledgement format to be used by
/// app-specific protocols.
/// NOTE: The field numbers 21 and 22 were explicitly chosen to avoid accidental
/// conflicts with other protobuf message formats used for acknowledgements.
/// The first byte of any message with this format will be the non-ASCII values
/// `0xaa` (result) or `0xb2` (error). Implemented as defined by ICS:
/// <https://github.com/cosmos/ibc/tree/master/spec/core/ics-004-channel-and-packet-semantics#acknowledgement-envelope>
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Acknowledgement {
    /// response contains either a result or an error and must be non-empty
    #[prost(oneof = "acknowledgement::Response", tags = "21, 22")]
    pub response: ::core::option::Option<acknowledgement::Response>,
}
/// Nested message and enum types in `Acknowledgement`.
pub mod acknowledgement {
    /// response contains either a result or an error and must be non-empty
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Response {
        #[prost(bytes, tag = "21")]
        Result(::prost::alloc::vec::Vec<u8>),
        #[prost(string, tag = "22")]
        Error(::prost::alloc::string::String),
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
    #[prost(message, repeated, tag = "1")]
    pub channels: ::prost::alloc::vec::Vec<IdentifiedChannel>,
    #[prost(message, repeated, tag = "2")]
    pub acknowledgements: ::prost::alloc::vec::Vec<PacketState>,
    #[prost(message, repeated, tag = "3")]
    pub commitments: ::prost::alloc::vec::Vec<PacketState>,
    #[prost(message, repeated, tag = "4")]
    pub receipts: ::prost::alloc::vec::Vec<PacketState>,
    #[prost(message, repeated, tag = "5")]
    pub send_sequences: ::prost::alloc::vec::Vec<PacketSequence>,
    #[prost(message, repeated, tag = "6")]
    pub recv_sequences: ::prost::alloc::vec::Vec<PacketSequence>,
    #[prost(message, repeated, tag = "7")]
    pub ack_sequences: ::prost::alloc::vec::Vec<PacketSequence>,
    /// the sequence for the next generated channel identifier
    #[prost(uint64, tag = "8")]
    pub next_channel_sequence: u64,
}
/// PacketSequence defines the genesis type necessary to retrieve and store
/// next send and receive sequences.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketSequence {
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    #[prost(uint64, tag = "3")]
    pub sequence: u64,
}
/// MsgChannelOpenInit defines an sdk.Msg to initialize a channel handshake. It
/// is called by a relayer on Chain A.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenInit {
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(message, optional, tag = "2")]
    pub channel: ::core::option::Option<Channel>,
    #[prost(string, tag = "3")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgChannelOpenInitResponse defines the Msg/ChannelOpenInit response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenInitResponse {
    #[prost(string, tag = "1")]
    pub channel_id: ::prost::alloc::string::String,
}
/// MsgChannelOpenInit defines a msg sent by a Relayer to try to open a channel
/// on Chain B. The version field within the Channel field has been deprecated. Its
/// value will be ignored by core IBC.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenTry {
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// in the case of crossing hello's, when both chains call OpenInit, we need
    /// the channel identifier of the previous channel in state INIT
    #[prost(string, tag = "2")]
    pub previous_channel_id: ::prost::alloc::string::String,
    /// NOTE: the version field within the channel has been deprecated. Its value will be ignored by core IBC.
    #[prost(message, optional, tag = "3")]
    pub channel: ::core::option::Option<Channel>,
    #[prost(string, tag = "4")]
    pub counterparty_version: ::prost::alloc::string::String,
    #[prost(bytes = "vec", tag = "5")]
    pub proof_init: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "6")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag = "7")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgChannelOpenTryResponse defines the Msg/ChannelOpenTry response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenTryResponse {}
/// MsgChannelOpenAck defines a msg sent by a Relayer to Chain A to acknowledge
/// the change of channel state to TRYOPEN on Chain B.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenAck {
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    #[prost(string, tag = "3")]
    pub counterparty_channel_id: ::prost::alloc::string::String,
    #[prost(string, tag = "4")]
    pub counterparty_version: ::prost::alloc::string::String,
    #[prost(bytes = "vec", tag = "5")]
    pub proof_try: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "6")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag = "7")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgChannelOpenAckResponse defines the Msg/ChannelOpenAck response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenAckResponse {}
/// MsgChannelOpenConfirm defines a msg sent by a Relayer to Chain B to
/// acknowledge the change of channel state to OPEN on Chain A.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenConfirm {
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    #[prost(bytes = "vec", tag = "3")]
    pub proof_ack: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "4")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag = "5")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgChannelOpenConfirmResponse defines the Msg/ChannelOpenConfirm response
/// type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenConfirmResponse {}
/// MsgChannelCloseInit defines a msg sent by a Relayer to Chain A
/// to close a channel with Chain B.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseInit {
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    #[prost(string, tag = "3")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgChannelCloseInitResponse defines the Msg/ChannelCloseInit response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseInitResponse {}
/// MsgChannelCloseConfirm defines a msg sent by a Relayer to Chain B
/// to acknowledge the change of channel state to CLOSED on Chain A.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseConfirm {
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    #[prost(bytes = "vec", tag = "3")]
    pub proof_init: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "4")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag = "5")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgChannelCloseConfirmResponse defines the Msg/ChannelCloseConfirm response
/// type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseConfirmResponse {}
/// MsgRecvPacket receives incoming IBC packet
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgRecvPacket {
    #[prost(message, optional, tag = "1")]
    pub packet: ::core::option::Option<Packet>,
    #[prost(bytes = "vec", tag = "2")]
    pub proof_commitment: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "3")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag = "4")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgRecvPacketResponse defines the Msg/RecvPacket response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgRecvPacketResponse {}
/// MsgTimeout receives timed-out packet
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeout {
    #[prost(message, optional, tag = "1")]
    pub packet: ::core::option::Option<Packet>,
    #[prost(bytes = "vec", tag = "2")]
    pub proof_unreceived: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "3")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(uint64, tag = "4")]
    pub next_sequence_recv: u64,
    #[prost(string, tag = "5")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgTimeoutResponse defines the Msg/Timeout response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeoutResponse {}
/// MsgTimeoutOnClose timed-out packet upon counterparty channel closure.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeoutOnClose {
    #[prost(message, optional, tag = "1")]
    pub packet: ::core::option::Option<Packet>,
    #[prost(bytes = "vec", tag = "2")]
    pub proof_unreceived: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "3")]
    pub proof_close: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "4")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(uint64, tag = "5")]
    pub next_sequence_recv: u64,
    #[prost(string, tag = "6")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgTimeoutOnCloseResponse defines the Msg/TimeoutOnClose response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeoutOnCloseResponse {}
/// MsgAcknowledgement receives incoming IBC acknowledgement
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgAcknowledgement {
    #[prost(message, optional, tag = "1")]
    pub packet: ::core::option::Option<Packet>,
    #[prost(bytes = "vec", tag = "2")]
    pub acknowledgement: ::prost::alloc::vec::Vec<u8>,
    #[prost(bytes = "vec", tag = "3")]
    pub proof_acked: ::prost::alloc::vec::Vec<u8>,
    #[prost(message, optional, tag = "4")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag = "5")]
    pub signer: ::prost::alloc::string::String,
}
/// MsgAcknowledgementResponse defines the Msg/Acknowledgement response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgAcknowledgementResponse {}
/// QueryChannelRequest is the request type for the Query/Channel RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
}
/// QueryChannelResponse is the response type for the Query/Channel RPC method.
/// Besides the Channel end, it includes a proof and the height from which the
/// proof was retrieved.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelResponse {
    /// channel associated with the request identifiers
    #[prost(message, optional, tag = "1")]
    pub channel: ::core::option::Option<Channel>,
    /// merkle proof of existence
    #[prost(bytes = "vec", tag = "2")]
    pub proof: ::prost::alloc::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag = "3")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryChannelsRequest is the request type for the Query/Channels RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelsRequest {
    /// pagination request
    #[prost(message, optional, tag = "1")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageRequest,
    >,
}
/// QueryChannelsResponse is the response type for the Query/Channels RPC method.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelsResponse {
    /// list of stored channels of the chain.
    #[prost(message, repeated, tag = "1")]
    pub channels: ::prost::alloc::vec::Vec<IdentifiedChannel>,
    /// pagination response
    #[prost(message, optional, tag = "2")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageResponse,
    >,
    /// query block height
    #[prost(message, optional, tag = "3")]
    pub height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryConnectionChannelsRequest is the request type for the
/// Query/QueryConnectionChannels RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConnectionChannelsRequest {
    /// connection unique identifier
    #[prost(string, tag = "1")]
    pub connection: ::prost::alloc::string::String,
    /// pagination request
    #[prost(message, optional, tag = "2")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageRequest,
    >,
}
/// QueryConnectionChannelsResponse is the Response type for the
/// Query/QueryConnectionChannels RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryConnectionChannelsResponse {
    /// list of channels associated with a connection.
    #[prost(message, repeated, tag = "1")]
    pub channels: ::prost::alloc::vec::Vec<IdentifiedChannel>,
    /// pagination response
    #[prost(message, optional, tag = "2")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageResponse,
    >,
    /// query block height
    #[prost(message, optional, tag = "3")]
    pub height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryChannelClientStateRequest is the request type for the Query/ClientState
/// RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelClientStateRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
}
/// QueryChannelClientStateResponse is the Response type for the
/// Query/QueryChannelClientState RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelClientStateResponse {
    /// client state associated with the channel
    #[prost(message, optional, tag = "1")]
    pub identified_client_state:
        ::core::option::Option<super::super::client::v1::IdentifiedClientState>,
    /// merkle proof of existence
    #[prost(bytes = "vec", tag = "2")]
    pub proof: ::prost::alloc::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag = "3")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryChannelConsensusStateRequest is the request type for the
/// Query/ConsensusState RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelConsensusStateRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// revision number of the consensus state
    #[prost(uint64, tag = "3")]
    pub revision_number: u64,
    /// revision height of the consensus state
    #[prost(uint64, tag = "4")]
    pub revision_height: u64,
}
/// QueryChannelClientStateResponse is the Response type for the
/// Query/QueryChannelClientState RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryChannelConsensusStateResponse {
    /// consensus state associated with the channel
    #[prost(message, optional, tag = "1")]
    pub consensus_state: ::core::option::Option<::prost_types::Any>,
    /// client ID associated with the consensus state
    #[prost(string, tag = "2")]
    pub client_id: ::prost::alloc::string::String,
    /// merkle proof of existence
    #[prost(bytes = "vec", tag = "3")]
    pub proof: ::prost::alloc::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag = "4")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketCommitmentRequest is the request type for the
/// Query/PacketCommitment RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// packet sequence
    #[prost(uint64, tag = "3")]
    pub sequence: u64,
}
/// QueryPacketCommitmentResponse defines the client query response for a packet
/// which also includes a proof and the height from which the proof was
/// retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentResponse {
    /// packet associated with the request fields
    #[prost(bytes = "vec", tag = "1")]
    pub commitment: ::prost::alloc::vec::Vec<u8>,
    /// merkle proof of existence
    #[prost(bytes = "vec", tag = "2")]
    pub proof: ::prost::alloc::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag = "3")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketCommitmentsRequest is the request type for the
/// Query/QueryPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentsRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// pagination request
    #[prost(message, optional, tag = "3")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageRequest,
    >,
}
/// QueryPacketCommitmentsResponse is the request type for the
/// Query/QueryPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentsResponse {
    #[prost(message, repeated, tag = "1")]
    pub commitments: ::prost::alloc::vec::Vec<PacketState>,
    /// pagination response
    #[prost(message, optional, tag = "2")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageResponse,
    >,
    /// query block height
    #[prost(message, optional, tag = "3")]
    pub height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketReceiptRequest is the request type for the
/// Query/PacketReceipt RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketReceiptRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// packet sequence
    #[prost(uint64, tag = "3")]
    pub sequence: u64,
}
/// QueryPacketReceiptResponse defines the client query response for a packet
/// receipt which also includes a proof, and the height from which the proof was
/// retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketReceiptResponse {
    /// success flag for if receipt exists
    #[prost(bool, tag = "2")]
    pub received: bool,
    /// merkle proof of existence
    #[prost(bytes = "vec", tag = "3")]
    pub proof: ::prost::alloc::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag = "4")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketAcknowledgementRequest is the request type for the
/// Query/PacketAcknowledgement RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// packet sequence
    #[prost(uint64, tag = "3")]
    pub sequence: u64,
}
/// QueryPacketAcknowledgementResponse defines the client query response for a
/// packet which also includes a proof and the height from which the
/// proof was retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementResponse {
    /// packet associated with the request fields
    #[prost(bytes = "vec", tag = "1")]
    pub acknowledgement: ::prost::alloc::vec::Vec<u8>,
    /// merkle proof of existence
    #[prost(bytes = "vec", tag = "2")]
    pub proof: ::prost::alloc::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag = "3")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketAcknowledgementsRequest is the request type for the
/// Query/QueryPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementsRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// pagination request
    #[prost(message, optional, tag = "3")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageRequest,
    >,
    /// list of packet sequences
    #[prost(uint64, repeated, tag = "4")]
    pub packet_commitment_sequences: ::prost::alloc::vec::Vec<u64>,
}
/// QueryPacketAcknowledgemetsResponse is the request type for the
/// Query/QueryPacketAcknowledgements RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementsResponse {
    #[prost(message, repeated, tag = "1")]
    pub acknowledgements: ::prost::alloc::vec::Vec<PacketState>,
    /// pagination response
    #[prost(message, optional, tag = "2")]
    pub pagination: ::core::option::Option<
        super::super::super::super::cosmos::base::query::v1beta1::PageResponse,
    >,
    /// query block height
    #[prost(message, optional, tag = "3")]
    pub height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryUnreceivedPacketsRequest is the request type for the
/// Query/UnreceivedPackets RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedPacketsRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// list of packet sequences
    #[prost(uint64, repeated, tag = "3")]
    pub packet_commitment_sequences: ::prost::alloc::vec::Vec<u64>,
}
/// QueryUnreceivedPacketsResponse is the response type for the
/// Query/UnreceivedPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedPacketsResponse {
    /// list of unreceived packet sequences
    #[prost(uint64, repeated, tag = "1")]
    pub sequences: ::prost::alloc::vec::Vec<u64>,
    /// query block height
    #[prost(message, optional, tag = "2")]
    pub height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryUnreceivedAcks is the request type for the
/// Query/UnreceivedAcks RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedAcksRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
    /// list of acknowledgement sequences
    #[prost(uint64, repeated, tag = "3")]
    pub packet_ack_sequences: ::prost::alloc::vec::Vec<u64>,
}
/// QueryUnreceivedAcksResponse is the response type for the
/// Query/UnreceivedAcks RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedAcksResponse {
    /// list of unreceived acknowledgement sequences
    #[prost(uint64, repeated, tag = "1")]
    pub sequences: ::prost::alloc::vec::Vec<u64>,
    /// query block height
    #[prost(message, optional, tag = "2")]
    pub height: ::core::option::Option<super::super::client::v1::Height>,
}
/// QueryNextSequenceReceiveRequest is the request type for the
/// Query/QueryNextSequenceReceiveRequest RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryNextSequenceReceiveRequest {
    /// port unique identifier
    #[prost(string, tag = "1")]
    pub port_id: ::prost::alloc::string::String,
    /// channel unique identifier
    #[prost(string, tag = "2")]
    pub channel_id: ::prost::alloc::string::String,
}
/// QuerySequenceResponse is the request type for the
/// Query/QueryNextSequenceReceiveResponse RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryNextSequenceReceiveResponse {
    /// next sequence receive number
    #[prost(uint64, tag = "1")]
    pub next_sequence_receive: u64,
    /// merkle proof of existence
    #[prost(bytes = "vec", tag = "2")]
    pub proof: ::prost::alloc::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag = "3")]
    pub proof_height: ::core::option::Option<super::super::client::v1::Height>,
}

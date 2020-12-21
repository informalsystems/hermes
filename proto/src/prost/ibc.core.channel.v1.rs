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
/// PacketState defines the generic type necessary to retrieve and store
/// packet commitments, acknowledgements, and receipts.
/// Caller is responsible for knowing the context necessary to interpret this
/// state as a commitment, acknowledgement, or a receipt.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketState {
    /// channel port identifier.
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier.
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// packet sequence.
    #[prost(uint64, tag="3")]
    pub sequence: u64,
    /// embedded data that represents packet state.
    #[prost(bytes, tag="4")]
    pub data: std::vec::Vec<u8>,
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
    pub acknowledgements: ::std::vec::Vec<PacketState>,
    #[prost(message, repeated, tag="3")]
    pub commitments: ::std::vec::Vec<PacketState>,
    #[prost(message, repeated, tag="4")]
    pub receipts: ::std::vec::Vec<PacketState>,
    #[prost(message, repeated, tag="5")]
    pub send_sequences: ::std::vec::Vec<PacketSequence>,
    #[prost(message, repeated, tag="6")]
    pub recv_sequences: ::std::vec::Vec<PacketSequence>,
    #[prost(message, repeated, tag="7")]
    pub ack_sequences: ::std::vec::Vec<PacketSequence>,
    /// the sequence for the next generated channel identifier
    #[prost(uint64, tag="8")]
    pub next_channel_sequence: u64,
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
/// MsgChannelOpenInit defines an sdk.Msg to initialize a channel handshake. It
/// is called by a relayer on Chain A.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenInit {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    #[prost(message, optional, tag="2")]
    pub channel: ::std::option::Option<Channel>,
    #[prost(string, tag="3")]
    pub signer: std::string::String,
}
/// MsgChannelOpenInitResponse defines the Msg/ChannelOpenInit response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenInitResponse {
}
/// MsgChannelOpenInit defines a msg sent by a Relayer to try to open a channel
/// on Chain B.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenTry {
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// in the case of crossing hello's, when both chains call OpenInit, we need the channel identifier
    /// of the previous channel in state INIT
    #[prost(string, tag="2")]
    pub previous_channel_id: std::string::String,
    #[prost(message, optional, tag="3")]
    pub channel: ::std::option::Option<Channel>,
    #[prost(string, tag="4")]
    pub counterparty_version: std::string::String,
    #[prost(bytes, tag="5")]
    pub proof_init: std::vec::Vec<u8>,
    #[prost(message, optional, tag="6")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="7")]
    pub signer: std::string::String,
}
/// MsgChannelOpenTryResponse defines the Msg/ChannelOpenTry response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenTryResponse {
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
/// MsgChannelOpenAckResponse defines the Msg/ChannelOpenAck response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenAckResponse {
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
/// MsgChannelOpenConfirmResponse defines the Msg/ChannelOpenConfirm response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelOpenConfirmResponse {
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
/// MsgChannelCloseInitResponse defines the Msg/ChannelCloseInit response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseInitResponse {
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
/// MsgChannelCloseConfirmResponse defines the Msg/ChannelCloseConfirm response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgChannelCloseConfirmResponse {
}
/// MsgRecvPacket receives incoming IBC packet
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgRecvPacket {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub proof_commitment: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="4")]
    pub signer: std::string::String,
}
/// MsgRecvPacketResponse defines the Msg/RecvPacket response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgRecvPacketResponse {
}
/// MsgTimeout receives timed-out packet
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeout {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub proof_unreceived: std::vec::Vec<u8>,
    #[prost(message, optional, tag="3")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(uint64, tag="4")]
    pub next_sequence_recv: u64,
    #[prost(string, tag="5")]
    pub signer: std::string::String,
}
/// MsgTimeoutResponse defines the Msg/Timeout response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeoutResponse {
}
/// MsgTimeoutOnClose timed-out packet upon counterparty channel closure.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeoutOnClose {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub proof_unreceived: std::vec::Vec<u8>,
    #[prost(bytes, tag="3")]
    pub proof_close: std::vec::Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(uint64, tag="5")]
    pub next_sequence_recv: u64,
    #[prost(string, tag="6")]
    pub signer: std::string::String,
}
/// MsgTimeoutOnCloseResponse defines the Msg/TimeoutOnClose response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgTimeoutOnCloseResponse {
}
/// MsgAcknowledgement receives incoming IBC acknowledgement
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgAcknowledgement {
    #[prost(message, optional, tag="1")]
    pub packet: ::std::option::Option<Packet>,
    #[prost(bytes, tag="2")]
    pub acknowledgement: std::vec::Vec<u8>,
    #[prost(bytes, tag="3")]
    pub proof_acked: std::vec::Vec<u8>,
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
    #[prost(string, tag="5")]
    pub signer: std::string::String,
}
/// MsgAcknowledgementResponse defines the Msg/Acknowledgement response type.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgAcknowledgementResponse {
}
# [doc = r" Generated client implementations."] pub mod msg_client { # ! [allow (unused_variables , dead_code , missing_docs)] use tonic :: codegen :: * ; # [doc = " Msg defines the ibc/channel Msg service."] pub struct MsgClient < T > { inner : tonic :: client :: Grpc < T > , } impl MsgClient < tonic :: transport :: Channel > { # [doc = r" Attempt to create a new client by connecting to a given endpoint."] pub async fn connect < D > (dst : D) -> Result < Self , tonic :: transport :: Error > where D : std :: convert :: TryInto < tonic :: transport :: Endpoint > , D :: Error : Into < StdError > , { let conn = tonic :: transport :: Endpoint :: new (dst) ? . connect () . await ? ; Ok (Self :: new (conn)) } } impl < T > MsgClient < T > where T : tonic :: client :: GrpcService < tonic :: body :: BoxBody > , T :: ResponseBody : Body + HttpBody + Send + 'static , T :: Error : Into < StdError > , < T :: ResponseBody as HttpBody > :: Error : Into < StdError > + Send , { pub fn new (inner : T) -> Self { let inner = tonic :: client :: Grpc :: new (inner) ; Self { inner } } pub fn with_interceptor (inner : T , interceptor : impl Into < tonic :: Interceptor >) -> Self { let inner = tonic :: client :: Grpc :: with_interceptor (inner , interceptor) ; Self { inner } } # [doc = " ChannelOpenInit defines a rpc handler method for MsgChannelOpenInit."] pub async fn channel_open_init (& mut self , request : impl tonic :: IntoRequest < super :: MsgChannelOpenInit > ,) -> Result < tonic :: Response < super :: MsgChannelOpenInitResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/ChannelOpenInit") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ChannelOpenTry defines a rpc handler method for MsgChannelOpenTry."] pub async fn channel_open_try (& mut self , request : impl tonic :: IntoRequest < super :: MsgChannelOpenTry > ,) -> Result < tonic :: Response < super :: MsgChannelOpenTryResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/ChannelOpenTry") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ChannelOpenAck defines a rpc handler method for MsgChannelOpenAck."] pub async fn channel_open_ack (& mut self , request : impl tonic :: IntoRequest < super :: MsgChannelOpenAck > ,) -> Result < tonic :: Response < super :: MsgChannelOpenAckResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/ChannelOpenAck") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ChannelOpenConfirm defines a rpc handler method for MsgChannelOpenConfirm."] pub async fn channel_open_confirm (& mut self , request : impl tonic :: IntoRequest < super :: MsgChannelOpenConfirm > ,) -> Result < tonic :: Response < super :: MsgChannelOpenConfirmResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/ChannelOpenConfirm") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ChannelCloseInit defines a rpc handler method for MsgChannelCloseInit."] pub async fn channel_close_init (& mut self , request : impl tonic :: IntoRequest < super :: MsgChannelCloseInit > ,) -> Result < tonic :: Response < super :: MsgChannelCloseInitResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/ChannelCloseInit") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ChannelCloseConfirm defines a rpc handler method for MsgChannelCloseConfirm."] pub async fn channel_close_confirm (& mut self , request : impl tonic :: IntoRequest < super :: MsgChannelCloseConfirm > ,) -> Result < tonic :: Response < super :: MsgChannelCloseConfirmResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/ChannelCloseConfirm") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " RecvPacket defines a rpc handler method for MsgRecvPacket."] pub async fn recv_packet (& mut self , request : impl tonic :: IntoRequest < super :: MsgRecvPacket > ,) -> Result < tonic :: Response < super :: MsgRecvPacketResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/RecvPacket") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " Timeout defines a rpc handler method for MsgTimeout."] pub async fn timeout (& mut self , request : impl tonic :: IntoRequest < super :: MsgTimeout > ,) -> Result < tonic :: Response < super :: MsgTimeoutResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/Timeout") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " TimeoutOnClose defines a rpc handler method for MsgTimeoutOnClose."] pub async fn timeout_on_close (& mut self , request : impl tonic :: IntoRequest < super :: MsgTimeoutOnClose > ,) -> Result < tonic :: Response < super :: MsgTimeoutOnCloseResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/TimeoutOnClose") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " Acknowledgement defines a rpc handler method for MsgAcknowledgement."] pub async fn acknowledgement (& mut self , request : impl tonic :: IntoRequest < super :: MsgAcknowledgement > ,) -> Result < tonic :: Response < super :: MsgAcknowledgementResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Msg/Acknowledgement") ; self . inner . unary (request . into_request () , path , codec) . await } } impl < T : Clone > Clone for MsgClient < T > { fn clone (& self) -> Self { Self { inner : self . inner . clone () , } } } impl < T > std :: fmt :: Debug for MsgClient < T > { fn fmt (& self , f : & mut std :: fmt :: Formatter < '_ >) -> std :: fmt :: Result { write ! (f , "MsgClient {{ ... }}") } } }/// QueryChannelRequest is the request type for the Query/Channel RPC method
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
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="3")]
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
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="3")]
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
    /// revision number of the consensus state
    #[prost(uint64, tag="3")]
    pub revision_number: u64,
    /// revision height of the consensus state
    #[prost(uint64, tag="4")]
    pub revision_height: u64,
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
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
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
/// which also includes a proof and the height from which the proof was
/// retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketCommitmentResponse {
    /// packet associated with the request fields
    #[prost(bytes, tag="1")]
    pub commitment: std::vec::Vec<u8>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="3")]
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
    pub commitments: ::std::vec::Vec<PacketState>,
    /// pagination response
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageResponse>,
    /// query block height
    #[prost(message, optional, tag="3")]
    pub height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketReceiptRequest is the request type for the
/// Query/PacketReceipt RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketReceiptRequest {
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
/// QueryPacketReceiptResponse defines the client query response for a packet receipt
/// which also includes a proof, and the height from which the proof was
/// retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketReceiptResponse {
    /// success flag for if receipt exists
    #[prost(bool, tag="2")]
    pub received: bool,
    /// merkle proof of existence
    #[prost(bytes, tag="3")]
    pub proof: std::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="4")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
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
/// packet which also includes a proof and the height from which the
/// proof was retrieved
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementResponse {
    /// packet associated with the request fields
    #[prost(bytes, tag="1")]
    pub acknowledgement: std::vec::Vec<u8>,
    /// merkle proof of existence
    #[prost(bytes, tag="2")]
    pub proof: std::vec::Vec<u8>,
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="3")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}
/// QueryPacketAcknowledgementsRequest is the request type for the
/// Query/QueryPacketCommitments RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementsRequest {
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
/// QueryPacketAcknowledgemetsResponse is the request type for the
/// Query/QueryPacketAcknowledgements RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryPacketAcknowledgementsResponse {
    #[prost(message, repeated, tag="1")]
    pub acknowledgements: ::std::vec::Vec<PacketState>,
    /// pagination response
    #[prost(message, optional, tag="2")]
    pub pagination: ::std::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageResponse>,
    /// query block height
    #[prost(message, optional, tag="3")]
    pub height: ::std::option::Option<super::super::client::v1::Height>,
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
/// QueryUnreceivedAcks is the request type for the
/// Query/UnreceivedAcks RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedAcksRequest {
    /// port unique identifier
    #[prost(string, tag="1")]
    pub port_id: std::string::String,
    /// channel unique identifier
    #[prost(string, tag="2")]
    pub channel_id: std::string::String,
    /// list of acknowledgement sequences
    #[prost(uint64, repeated, tag="3")]
    pub packet_ack_sequences: ::std::vec::Vec<u64>,
}
/// QueryUnreceivedAcksResponse is the response type for the
/// Query/UnreceivedAcks RPC method
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUnreceivedAcksResponse {
    /// list of unreceived acknowledgement sequences
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
    /// height at which the proof was retrieved
    #[prost(message, optional, tag="3")]
    pub proof_height: ::std::option::Option<super::super::client::v1::Height>,
}
# [doc = r" Generated client implementations."] pub mod query_client { # ! [allow (unused_variables , dead_code , missing_docs)] use tonic :: codegen :: * ; # [doc = " Query provides defines the gRPC querier service"] pub struct QueryClient < T > { inner : tonic :: client :: Grpc < T > , } impl QueryClient < tonic :: transport :: Channel > { # [doc = r" Attempt to create a new client by connecting to a given endpoint."] pub async fn connect < D > (dst : D) -> Result < Self , tonic :: transport :: Error > where D : std :: convert :: TryInto < tonic :: transport :: Endpoint > , D :: Error : Into < StdError > , { let conn = tonic :: transport :: Endpoint :: new (dst) ? . connect () . await ? ; Ok (Self :: new (conn)) } } impl < T > QueryClient < T > where T : tonic :: client :: GrpcService < tonic :: body :: BoxBody > , T :: ResponseBody : Body + HttpBody + Send + 'static , T :: Error : Into < StdError > , < T :: ResponseBody as HttpBody > :: Error : Into < StdError > + Send , { pub fn new (inner : T) -> Self { let inner = tonic :: client :: Grpc :: new (inner) ; Self { inner } } pub fn with_interceptor (inner : T , interceptor : impl Into < tonic :: Interceptor >) -> Self { let inner = tonic :: client :: Grpc :: with_interceptor (inner , interceptor) ; Self { inner } } # [doc = " Channel queries an IBC Channel."] pub async fn channel (& mut self , request : impl tonic :: IntoRequest < super :: QueryChannelRequest > ,) -> Result < tonic :: Response < super :: QueryChannelResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/Channel") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " Channels queries all the IBC channels of a chain."] pub async fn channels (& mut self , request : impl tonic :: IntoRequest < super :: QueryChannelsRequest > ,) -> Result < tonic :: Response < super :: QueryChannelsResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/Channels") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ConnectionChannels queries all the channels associated with a connection"] # [doc = " end."] pub async fn connection_channels (& mut self , request : impl tonic :: IntoRequest < super :: QueryConnectionChannelsRequest > ,) -> Result < tonic :: Response < super :: QueryConnectionChannelsResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/ConnectionChannels") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ChannelClientState queries for the client state for the channel associated"] # [doc = " with the provided channel identifiers."] pub async fn channel_client_state (& mut self , request : impl tonic :: IntoRequest < super :: QueryChannelClientStateRequest > ,) -> Result < tonic :: Response < super :: QueryChannelClientStateResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/ChannelClientState") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " ChannelConsensusState queries for the consensus state for the channel"] # [doc = " associated with the provided channel identifiers."] pub async fn channel_consensus_state (& mut self , request : impl tonic :: IntoRequest < super :: QueryChannelConsensusStateRequest > ,) -> Result < tonic :: Response < super :: QueryChannelConsensusStateResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/ChannelConsensusState") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " PacketCommitment queries a stored packet commitment hash."] pub async fn packet_commitment (& mut self , request : impl tonic :: IntoRequest < super :: QueryPacketCommitmentRequest > ,) -> Result < tonic :: Response < super :: QueryPacketCommitmentResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/PacketCommitment") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " PacketCommitments returns all the packet commitments hashes associated"] # [doc = " with a channel."] pub async fn packet_commitments (& mut self , request : impl tonic :: IntoRequest < super :: QueryPacketCommitmentsRequest > ,) -> Result < tonic :: Response < super :: QueryPacketCommitmentsResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/PacketCommitments") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " PacketReceipt queries if a given packet sequence has been received on the queried chain"] pub async fn packet_receipt (& mut self , request : impl tonic :: IntoRequest < super :: QueryPacketReceiptRequest > ,) -> Result < tonic :: Response < super :: QueryPacketReceiptResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/PacketReceipt") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " PacketAcknowledgement queries a stored packet acknowledgement hash."] pub async fn packet_acknowledgement (& mut self , request : impl tonic :: IntoRequest < super :: QueryPacketAcknowledgementRequest > ,) -> Result < tonic :: Response < super :: QueryPacketAcknowledgementResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/PacketAcknowledgement") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " PacketAcknowledgements returns all the packet acknowledgements associated"] # [doc = " with a channel."] pub async fn packet_acknowledgements (& mut self , request : impl tonic :: IntoRequest < super :: QueryPacketAcknowledgementsRequest > ,) -> Result < tonic :: Response < super :: QueryPacketAcknowledgementsResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/PacketAcknowledgements") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " UnreceivedPackets returns all the unreceived IBC packets associated with a"] # [doc = " channel and sequences."] pub async fn unreceived_packets (& mut self , request : impl tonic :: IntoRequest < super :: QueryUnreceivedPacketsRequest > ,) -> Result < tonic :: Response < super :: QueryUnreceivedPacketsResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/UnreceivedPackets") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " UnreceivedAcks returns all the unreceived IBC acknowledgements associated with a"] # [doc = " channel and sequences."] pub async fn unreceived_acks (& mut self , request : impl tonic :: IntoRequest < super :: QueryUnreceivedAcksRequest > ,) -> Result < tonic :: Response < super :: QueryUnreceivedAcksResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/UnreceivedAcks") ; self . inner . unary (request . into_request () , path , codec) . await } # [doc = " NextSequenceReceive returns the next receive sequence for a given channel."] pub async fn next_sequence_receive (& mut self , request : impl tonic :: IntoRequest < super :: QueryNextSequenceReceiveRequest > ,) -> Result < tonic :: Response < super :: QueryNextSequenceReceiveResponse > , tonic :: Status > { self . inner . ready () . await . map_err (| e | { tonic :: Status :: new (tonic :: Code :: Unknown , format ! ("Service was not ready: {}" , e . into ())) }) ? ; let codec = tonic :: codec :: ProstCodec :: default () ; let path = http :: uri :: PathAndQuery :: from_static ("/ibc.core.channel.v1.Query/NextSequenceReceive") ; self . inner . unary (request . into_request () , path , codec) . await } } impl < T : Clone > Clone for QueryClient < T > { fn clone (& self) -> Self { Self { inner : self . inner . clone () , } } } impl < T > std :: fmt :: Debug for QueryClient < T > { fn fmt (& self , f : & mut std :: fmt :: Formatter < '_ >) -> std :: fmt :: Result { write ! (f , "QueryClient {{ ... }}") } } }
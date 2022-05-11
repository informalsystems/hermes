/// Metadata defines the ICS29 channel specific metadata encoded into the channel version bytestring
/// See ICS004: <https://github.com/cosmos/ibc/tree/master/spec/core/ics-004-channel-and-packet-semantics#Versioning>
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Metadata {
    /// fee_version defines the ICS29 fee version
    #[prost(string, tag="1")]
    pub fee_version: ::prost::alloc::string::String,
    /// app_version defines the underlying application version, which may or may not be a JSON encoded bytestring
    #[prost(string, tag="2")]
    pub app_version: ::prost::alloc::string::String,
}
/// Fee defines the ICS29 receive, acknowledgement and timeout fees
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Fee {
    /// the packet receive fee
    #[prost(message, repeated, tag="1")]
    pub recv_fee: ::prost::alloc::vec::Vec<super::super::super::super::cosmos::base::v1beta1::Coin>,
    /// the packet acknowledgement fee
    #[prost(message, repeated, tag="2")]
    pub ack_fee: ::prost::alloc::vec::Vec<super::super::super::super::cosmos::base::v1beta1::Coin>,
    /// the packet timeout fee
    #[prost(message, repeated, tag="3")]
    pub timeout_fee: ::prost::alloc::vec::Vec<super::super::super::super::cosmos::base::v1beta1::Coin>,
}
/// PacketFee contains ICS29 relayer fees, refund address and optional list of permitted relayers
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketFee {
    /// fee encapsulates the recv, ack and timeout fees associated with an IBC packet
    #[prost(message, optional, tag="1")]
    pub fee: ::core::option::Option<Fee>,
    /// the refund address for unspent fees
    #[prost(string, tag="2")]
    pub refund_address: ::prost::alloc::string::String,
    /// optional list of relayers permitted to receive fees
    #[prost(string, repeated, tag="3")]
    pub relayers: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
}
/// PacketFees contains a list of type PacketFee
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PacketFees {
    /// list of packet fees
    #[prost(message, repeated, tag="1")]
    pub packet_fees: ::prost::alloc::vec::Vec<PacketFee>,
}
/// IdentifiedPacketFees contains a list of type PacketFee and associated PacketId
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct IdentifiedPacketFees {
    /// unique packet identifier comprised of the channel ID, port ID and sequence
    #[prost(message, optional, tag="1")]
    pub packet_id: ::core::option::Option<super::super::super::core::channel::v1::PacketId>,
    /// list of packet fees
    #[prost(message, repeated, tag="2")]
    pub packet_fees: ::prost::alloc::vec::Vec<PacketFee>,
}
/// MsgRegisterCounterpartyAddress defines the request type for the RegisterCounterpartyAddress rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgRegisterCounterpartyAddress {
    /// the relayer address
    #[prost(string, tag="1")]
    pub address: ::prost::alloc::string::String,
    /// the counterparty relayer address
    #[prost(string, tag="2")]
    pub counterparty_address: ::prost::alloc::string::String,
    /// unique channel identifier
    #[prost(string, tag="3")]
    pub channel_id: ::prost::alloc::string::String,
}
/// MsgRegisterCounterpartyAddressResponse defines the response type for the RegisterCounterpartyAddress rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgRegisterCounterpartyAddressResponse {
}
/// MsgPayPacketFee defines the request type for the PayPacketFee rpc
/// This Msg can be used to pay for a packet at the next sequence send & should be combined with the Msg that will be
/// paid for
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgPayPacketFee {
    /// fee encapsulates the recv, ack and timeout fees associated with an IBC packet
    #[prost(message, optional, tag="1")]
    pub fee: ::core::option::Option<Fee>,
    /// the source port unique identifier
    #[prost(string, tag="2")]
    pub source_port_id: ::prost::alloc::string::String,
    /// the source channel unique identifer
    #[prost(string, tag="3")]
    pub source_channel_id: ::prost::alloc::string::String,
    /// account address to refund fee if necessary
    #[prost(string, tag="4")]
    pub signer: ::prost::alloc::string::String,
    /// optional list of relayers permitted to the receive packet fees
    #[prost(string, repeated, tag="5")]
    pub relayers: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
}
/// MsgPayPacketFeeResponse defines the response type for the PayPacketFee rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgPayPacketFeeResponse {
}
/// MsgPayPacketFeeAsync defines the request type for the PayPacketFeeAsync rpc
/// This Msg can be used to pay for a packet at a specified sequence (instead of the next sequence send)
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgPayPacketFeeAsync {
    /// unique packet identifier comprised of the channel ID, port ID and sequence
    #[prost(message, optional, tag="1")]
    pub packet_id: ::core::option::Option<super::super::super::core::channel::v1::PacketId>,
    /// the packet fee associated with a particular IBC packet
    #[prost(message, optional, tag="2")]
    pub packet_fee: ::core::option::Option<PacketFee>,
}
/// MsgPayPacketFeeAsyncResponse defines the response type for the PayPacketFeeAsync rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgPayPacketFeeAsyncResponse {
}
/// Generated client implementations.
#[cfg(feature = "client")]
pub mod msg_client {
    #![allow(unused_variables, dead_code, missing_docs, clippy::let_unit_value)]
    use tonic::codegen::*;
    /// Msg defines the ICS29 Msg service.
    #[derive(Debug, Clone)]
    pub struct MsgClient<T> {
        inner: tonic::client::Grpc<T>,
    }
    impl MsgClient<tonic::transport::Channel> {
        /// Attempt to create a new client by connecting to a given endpoint.
        pub async fn connect<D>(dst: D) -> Result<Self, tonic::transport::Error>
        where
            D: std::convert::TryInto<tonic::transport::Endpoint>,
            D::Error: Into<StdError>,
        {
            let conn = tonic::transport::Endpoint::new(dst)?.connect().await?;
            Ok(Self::new(conn))
        }
    }
    impl<T> MsgClient<T>
    where
        T: tonic::client::GrpcService<tonic::body::BoxBody>,
        T::Error: Into<StdError>,
        T::ResponseBody: Default + Body<Data = Bytes> + Send + 'static,
        <T::ResponseBody as Body>::Error: Into<StdError> + Send,
    {
        pub fn new(inner: T) -> Self {
            let inner = tonic::client::Grpc::new(inner);
            Self { inner }
        }
        pub fn with_interceptor<F>(
            inner: T,
            interceptor: F,
        ) -> MsgClient<InterceptedService<T, F>>
        where
            F: tonic::service::Interceptor,
            T: tonic::codegen::Service<
                http::Request<tonic::body::BoxBody>,
                Response = http::Response<
                    <T as tonic::client::GrpcService<tonic::body::BoxBody>>::ResponseBody,
                >,
            >,
            <T as tonic::codegen::Service<
                http::Request<tonic::body::BoxBody>,
            >>::Error: Into<StdError> + Send + Sync,
        {
            MsgClient::new(InterceptedService::new(inner, interceptor))
        }
        /// Compress requests with `gzip`.
        ///
        /// This requires the server to support it otherwise it might respond with an
        /// error.
        #[must_use]
        pub fn send_gzip(mut self) -> Self {
            self.inner = self.inner.send_gzip();
            self
        }
        /// Enable decompressing responses with `gzip`.
        #[must_use]
        pub fn accept_gzip(mut self) -> Self {
            self.inner = self.inner.accept_gzip();
            self
        }
        /// RegisterCounterpartyAddress defines a rpc handler method for MsgRegisterCounterpartyAddress
        /// RegisterCounterpartyAddress is called by the relayer on each channelEnd and allows them to specify their
        /// counterparty address before relaying. This ensures they will be properly compensated for forward relaying since
        /// destination chain must send back relayer's source address (counterparty address) in acknowledgement. This function
        /// may be called more than once by a relayer, in which case, latest counterparty address is always used.
        pub async fn register_counterparty_address(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgRegisterCounterpartyAddress>,
        ) -> Result<
                tonic::Response<super::MsgRegisterCounterpartyAddressResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Msg/RegisterCounterpartyAddress",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// PayPacketFee defines a rpc handler method for MsgPayPacketFee
        /// PayPacketFee is an open callback that may be called by any module/user that wishes to escrow funds in order to
        /// incentivize the relaying of the packet at the next sequence
        /// NOTE: This method is intended to be used within a multi msg transaction, where the subsequent msg that follows
        /// initiates the lifecycle of the incentivized packet
        pub async fn pay_packet_fee(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgPayPacketFee>,
        ) -> Result<tonic::Response<super::MsgPayPacketFeeResponse>, tonic::Status> {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Msg/PayPacketFee",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// PayPacketFeeAsync defines a rpc handler method for MsgPayPacketFeeAsync
        /// PayPacketFeeAsync is an open callback that may be called by any module/user that wishes to escrow funds in order to
        /// incentivize the relaying of a known packet (i.e. at a particular sequence)
        pub async fn pay_packet_fee_async(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgPayPacketFeeAsync>,
        ) -> Result<
                tonic::Response<super::MsgPayPacketFeeAsyncResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Msg/PayPacketFeeAsync",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
    }
}
/// GenesisState defines the ICS29 fee middleware genesis state
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GenesisState {
    /// list of identified packet fees
    #[prost(message, repeated, tag="1")]
    pub identified_fees: ::prost::alloc::vec::Vec<IdentifiedPacketFees>,
    /// list of fee enabled channels
    #[prost(message, repeated, tag="2")]
    pub fee_enabled_channels: ::prost::alloc::vec::Vec<FeeEnabledChannel>,
    /// list of registered relayer addresses
    #[prost(message, repeated, tag="3")]
    pub registered_relayers: ::prost::alloc::vec::Vec<RegisteredRelayerAddress>,
    /// list of forward relayer addresses
    #[prost(message, repeated, tag="4")]
    pub forward_relayers: ::prost::alloc::vec::Vec<ForwardRelayerAddress>,
}
/// FeeEnabledChannel contains the PortID & ChannelID for a fee enabled channel
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct FeeEnabledChannel {
    /// unique port identifier
    #[prost(string, tag="1")]
    pub port_id: ::prost::alloc::string::String,
    /// unique channel identifier
    #[prost(string, tag="2")]
    pub channel_id: ::prost::alloc::string::String,
}
/// RegisteredRelayerAddress contains the address and counterparty address for a specific relayer (for distributing fees)
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct RegisteredRelayerAddress {
    /// the relayer address
    #[prost(string, tag="1")]
    pub address: ::prost::alloc::string::String,
    /// the counterparty relayer address
    #[prost(string, tag="2")]
    pub counterparty_address: ::prost::alloc::string::String,
    /// unique channel identifier
    #[prost(string, tag="3")]
    pub channel_id: ::prost::alloc::string::String,
}
/// ForwardRelayerAddress contains the forward relayer address and PacketId used for async acknowledgements
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ForwardRelayerAddress {
    /// the forward relayer address
    #[prost(string, tag="1")]
    pub address: ::prost::alloc::string::String,
    /// unique packet identifer comprised of the channel ID, port ID and sequence
    #[prost(message, optional, tag="2")]
    pub packet_id: ::core::option::Option<super::super::super::core::channel::v1::PacketId>,
}
/// QueryIncentivizedPacketsRequest defines the request type for the IncentivizedPackets rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryIncentivizedPacketsRequest {
    /// pagination defines an optional pagination for the request.
    #[prost(message, optional, tag="1")]
    pub pagination: ::core::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageRequest>,
    /// block height at which to query
    #[prost(uint64, tag="2")]
    pub query_height: u64,
}
/// QueryIncentivizedPacketsResponse defines the response type for the IncentivizedPackets rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryIncentivizedPacketsResponse {
    /// list of identified fees for incentivized packets
    #[prost(message, repeated, tag="1")]
    pub incentivized_packets: ::prost::alloc::vec::Vec<IdentifiedPacketFees>,
}
/// QueryIncentivizedPacketRequest defines the request type for the IncentivizedPacket rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryIncentivizedPacketRequest {
    /// unique packet identifier comprised of channel ID, port ID and sequence
    #[prost(message, optional, tag="1")]
    pub packet_id: ::core::option::Option<super::super::super::core::channel::v1::PacketId>,
    /// block height at which to query
    #[prost(uint64, tag="2")]
    pub query_height: u64,
}
/// QueryIncentivizedPacketsResponse defines the response type for the IncentivizedPacket rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryIncentivizedPacketResponse {
    /// the identified fees for the incentivized packet
    #[prost(message, optional, tag="1")]
    pub incentivized_packet: ::core::option::Option<IdentifiedPacketFees>,
}
/// QueryIncentivizedPacketsForChannelRequest defines the request type for querying for all incentivized packets
/// for a specific channel
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryIncentivizedPacketsForChannelRequest {
    /// pagination defines an optional pagination for the request.
    #[prost(message, optional, tag="1")]
    pub pagination: ::core::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageRequest>,
    #[prost(string, tag="2")]
    pub port_id: ::prost::alloc::string::String,
    #[prost(string, tag="3")]
    pub channel_id: ::prost::alloc::string::String,
    /// Height to query at
    #[prost(uint64, tag="4")]
    pub query_height: u64,
}
/// QueryIncentivizedPacketsResponse defines the response type for the incentivized packets RPC
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryIncentivizedPacketsForChannelResponse {
    /// Map of all incentivized_packets
    #[prost(message, repeated, tag="1")]
    pub incentivized_packets: ::prost::alloc::vec::Vec<IdentifiedPacketFees>,
}
/// QueryTotalRecvFeesRequest defines the request type for the TotalRecvFees rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryTotalRecvFeesRequest {
    /// the packet identifier for the associated fees
    #[prost(message, optional, tag="1")]
    pub packet_id: ::core::option::Option<super::super::super::core::channel::v1::PacketId>,
}
/// QueryTotalRecvFeesResponse defines the response type for the TotalRecvFees rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryTotalRecvFeesResponse {
    /// the total packet receive fees
    #[prost(message, repeated, tag="1")]
    pub recv_fees: ::prost::alloc::vec::Vec<super::super::super::super::cosmos::base::v1beta1::Coin>,
}
/// QueryTotalAckFeesRequest defines the request type for the TotalAckFees rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryTotalAckFeesRequest {
    /// the packet identifier for the associated fees
    #[prost(message, optional, tag="1")]
    pub packet_id: ::core::option::Option<super::super::super::core::channel::v1::PacketId>,
}
/// QueryTotalAckFeesResponse defines the response type for the TotalAckFees rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryTotalAckFeesResponse {
    /// the total packet acknowledgement fees
    #[prost(message, repeated, tag="1")]
    pub ack_fees: ::prost::alloc::vec::Vec<super::super::super::super::cosmos::base::v1beta1::Coin>,
}
/// QueryTotalTimeoutFeesRequest defines the request type for the TotalTimeoutFees rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryTotalTimeoutFeesRequest {
    /// the packet identifier for the associated fees
    #[prost(message, optional, tag="1")]
    pub packet_id: ::core::option::Option<super::super::super::core::channel::v1::PacketId>,
}
/// QueryTotalTimeoutFeesResponse defines the response type for the TotalTimeoutFees rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryTotalTimeoutFeesResponse {
    /// the total packet timeout fees
    #[prost(message, repeated, tag="1")]
    pub timeout_fees: ::prost::alloc::vec::Vec<super::super::super::super::cosmos::base::v1beta1::Coin>,
}
/// QueryCounterpartyAddressRequest defines the request type for the CounterpartyAddress rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCounterpartyAddressRequest {
    /// unique channel identifier
    #[prost(string, tag="1")]
    pub channel_id: ::prost::alloc::string::String,
    /// the relayer address to which the counterparty is registered
    #[prost(string, tag="2")]
    pub relayer_address: ::prost::alloc::string::String,
}
/// QueryCounterpartyAddressResponse defines the response type for the CounterpartyAddress rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCounterpartyAddressResponse {
    /// the counterparty address used to compensate forward relaying
    #[prost(string, tag="1")]
    pub counterparty_address: ::prost::alloc::string::String,
}
/// QueryFeeEnabledChannelsRequest defines the request type for the FeeEnabledChannels rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryFeeEnabledChannelsRequest {
    /// pagination defines an optional pagination for the request.
    #[prost(message, optional, tag="1")]
    pub pagination: ::core::option::Option<super::super::super::super::cosmos::base::query::v1beta1::PageRequest>,
    /// block height at which to query
    #[prost(uint64, tag="2")]
    pub query_height: u64,
}
/// QueryFeeEnabledChannelsResponse defines the response type for the FeeEnabledChannels rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryFeeEnabledChannelsResponse {
    /// list of fee enabled channels
    #[prost(message, repeated, tag="1")]
    pub fee_enabled_channels: ::prost::alloc::vec::Vec<FeeEnabledChannel>,
}
/// QueryFeeEnabledChannelRequest defines the request type for the FeeEnabledChannel rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryFeeEnabledChannelRequest {
    /// unique port identifier
    #[prost(string, tag="1")]
    pub port_id: ::prost::alloc::string::String,
    /// unique channel identifier
    #[prost(string, tag="2")]
    pub channel_id: ::prost::alloc::string::String,
}
/// QueryFeeEnabledChannelResponse defines the response type for the FeeEnabledChannel rpc
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryFeeEnabledChannelResponse {
    /// boolean flag representing the fee enabled channel status
    #[prost(bool, tag="1")]
    pub fee_enabled: bool,
}
/// Generated client implementations.
#[cfg(feature = "client")]
pub mod query_client {
    #![allow(unused_variables, dead_code, missing_docs, clippy::let_unit_value)]
    use tonic::codegen::*;
    /// Query defines the ICS29 gRPC querier service.
    #[derive(Debug, Clone)]
    pub struct QueryClient<T> {
        inner: tonic::client::Grpc<T>,
    }
    impl QueryClient<tonic::transport::Channel> {
        /// Attempt to create a new client by connecting to a given endpoint.
        pub async fn connect<D>(dst: D) -> Result<Self, tonic::transport::Error>
        where
            D: std::convert::TryInto<tonic::transport::Endpoint>,
            D::Error: Into<StdError>,
        {
            let conn = tonic::transport::Endpoint::new(dst)?.connect().await?;
            Ok(Self::new(conn))
        }
    }
    impl<T> QueryClient<T>
    where
        T: tonic::client::GrpcService<tonic::body::BoxBody>,
        T::Error: Into<StdError>,
        T::ResponseBody: Default + Body<Data = Bytes> + Send + 'static,
        <T::ResponseBody as Body>::Error: Into<StdError> + Send,
    {
        pub fn new(inner: T) -> Self {
            let inner = tonic::client::Grpc::new(inner);
            Self { inner }
        }
        pub fn with_interceptor<F>(
            inner: T,
            interceptor: F,
        ) -> QueryClient<InterceptedService<T, F>>
        where
            F: tonic::service::Interceptor,
            T: tonic::codegen::Service<
                http::Request<tonic::body::BoxBody>,
                Response = http::Response<
                    <T as tonic::client::GrpcService<tonic::body::BoxBody>>::ResponseBody,
                >,
            >,
            <T as tonic::codegen::Service<
                http::Request<tonic::body::BoxBody>,
            >>::Error: Into<StdError> + Send + Sync,
        {
            QueryClient::new(InterceptedService::new(inner, interceptor))
        }
        /// Compress requests with `gzip`.
        ///
        /// This requires the server to support it otherwise it might respond with an
        /// error.
        #[must_use]
        pub fn send_gzip(mut self) -> Self {
            self.inner = self.inner.send_gzip();
            self
        }
        /// Enable decompressing responses with `gzip`.
        #[must_use]
        pub fn accept_gzip(mut self) -> Self {
            self.inner = self.inner.accept_gzip();
            self
        }
        /// IncentivizedPackets returns all incentivized packets and their associated fees
        pub async fn incentivized_packets(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryIncentivizedPacketsRequest>,
        ) -> Result<
                tonic::Response<super::QueryIncentivizedPacketsResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/IncentivizedPackets",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// IncentivizedPacket returns all packet fees for a packet given its identifier
        pub async fn incentivized_packet(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryIncentivizedPacketRequest>,
        ) -> Result<
                tonic::Response<super::QueryIncentivizedPacketResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/IncentivizedPacket",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// Gets all incentivized packets for a specific channel
        pub async fn incentivized_packets_for_channel(
            &mut self,
            request: impl tonic::IntoRequest<
                super::QueryIncentivizedPacketsForChannelRequest,
            >,
        ) -> Result<
                tonic::Response<super::QueryIncentivizedPacketsForChannelResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/IncentivizedPacketsForChannel",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// TotalRecvFees returns the total receive fees for a packet given its identifier
        pub async fn total_recv_fees(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryTotalRecvFeesRequest>,
        ) -> Result<tonic::Response<super::QueryTotalRecvFeesResponse>, tonic::Status> {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/TotalRecvFees",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// TotalAckFees returns the total acknowledgement fees for a packet given its identifier
        pub async fn total_ack_fees(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryTotalAckFeesRequest>,
        ) -> Result<tonic::Response<super::QueryTotalAckFeesResponse>, tonic::Status> {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/TotalAckFees",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// TotalTimeoutFees returns the total timeout fees for a packet given its identifier
        pub async fn total_timeout_fees(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryTotalTimeoutFeesRequest>,
        ) -> Result<
                tonic::Response<super::QueryTotalTimeoutFeesResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/TotalTimeoutFees",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// CounterpartyAddress returns the registered counterparty address for forward relaying
        pub async fn counterparty_address(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryCounterpartyAddressRequest>,
        ) -> Result<
                tonic::Response<super::QueryCounterpartyAddressResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/CounterpartyAddress",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// FeeEnabledChannels returns a list of all fee enabled channels
        pub async fn fee_enabled_channels(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryFeeEnabledChannelsRequest>,
        ) -> Result<
                tonic::Response<super::QueryFeeEnabledChannelsResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/FeeEnabledChannels",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// FeeEnabledChannel returns true if the provided port and channel identifiers belong to a fee enabled channel
        pub async fn fee_enabled_channel(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryFeeEnabledChannelRequest>,
        ) -> Result<
                tonic::Response<super::QueryFeeEnabledChannelResponse>,
                tonic::Status,
            > {
            self.inner
                .ready()
                .await
                .map_err(|e| {
                    tonic::Status::new(
                        tonic::Code::Unknown,
                        format!("Service was not ready: {}", e.into()),
                    )
                })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.applications.fee.v1.Query/FeeEnabledChannel",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
    }
}
/// IncentivizedAcknowledgement is the acknowledgement format to be used by applications wrapped in the fee middleware
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct IncentivizedAcknowledgement {
    /// the underlying app acknowledgement bytes
    #[prost(bytes="vec", tag="1")]
    pub app_acknowledgement: ::prost::alloc::vec::Vec<u8>,
    /// the relayer address which submits the recv packet message
    #[prost(string, tag="2")]
    pub forward_relayer_address: ::prost::alloc::string::String,
    /// success flag of the base application callback
    #[prost(bool, tag="3")]
    pub underlying_app_success: bool,
}

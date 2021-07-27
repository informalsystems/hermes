use ibc_proto::ibc::core::channel::v1::{
    QueryChannelRequest,
    QueryChannelResponse,
    QueryChannelsRequest,
    QueryChannelsResponse,
    QueryConnectionChannelsRequest,
    QueryConnectionChannelsResponse,
    QueryChannelClientStateRequest,
    QueryChannelClientStateResponse,
    QueryChannelConsensusStateRequest,
    QueryChannelConsensusStateResponse,
    QueryPacketCommitmentRequest,
    QueryPacketCommitmentResponse,
    QueryPacketCommitmentsRequest,
    QueryPacketCommitmentsResponse,
    QueryPacketReceiptRequest,
    QueryPacketReceiptResponse,
    QueryPacketAcknowledgementRequest,
    QueryPacketAcknowledgementResponse,
    QueryPacketAcknowledgementsRequest,
    QueryPacketAcknowledgementsResponse,
    QueryUnreceivedPacketsRequest,
    QueryUnreceivedPacketsResponse,
    QueryUnreceivedAcksRequest,
    QueryUnreceivedAcksResponse,
    QueryNextSequenceReceiveRequest,
    QueryNextSequenceReceiveResponse
};

#[doc = r" Generated client implementations."]
pub mod query_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Query provides defines the gRPC querier service"]
    pub struct QueryClient<T> {
        inner: tonic::client::Grpc<T>,
    }
    impl QueryClient<tonic::transport::Channel> {
        #[doc = r" Attempt to create a new client by connecting to a given endpoint."]
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
        T::ResponseBody: Body + HttpBody + Send + 'static,
        T::Error: Into<StdError>,
        <T::ResponseBody as HttpBody>::Error: Into<StdError> + Send,
    {
        pub fn new(inner: T) -> Self {
            let inner = tonic::client::Grpc::new(inner);
            Self { inner }
        }
        pub fn with_interceptor(inner: T, interceptor: impl Into<tonic::Interceptor>) -> Self {
            let inner = tonic::client::Grpc::with_interceptor(inner, interceptor);
            Self { inner }
        }
        #[doc = " Channel queries an IBC Channel."]
        pub async fn channel(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryChannelRequest>,
        ) -> Result<tonic::Response<super::QueryChannelResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Query/Channel");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Channels queries all the IBC channels of a chain."]
        pub async fn channels(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryChannelsRequest>,
        ) -> Result<tonic::Response<super::QueryChannelsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Query/Channels");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ConnectionChannels queries all the channels associated with a connection"]
        #[doc = " end."]
        pub async fn connection_channels(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryConnectionChannelsRequest>,
        ) -> Result<tonic::Response<super::QueryConnectionChannelsResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/ConnectionChannels",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ChannelClientState queries for the client state for the channel associated"]
        #[doc = " with the provided channel identifiers."]
        pub async fn channel_client_state(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryChannelClientStateRequest>,
        ) -> Result<tonic::Response<super::QueryChannelClientStateResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/ChannelClientState",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ChannelConsensusState queries for the consensus state for the channel"]
        #[doc = " associated with the provided channel identifiers."]
        pub async fn channel_consensus_state(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryChannelConsensusStateRequest>,
        ) -> Result<tonic::Response<super::QueryChannelConsensusStateResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/ChannelConsensusState",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " PacketCommitment queries a stored packet commitment hash."]
        pub async fn packet_commitment(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryPacketCommitmentRequest>,
        ) -> Result<tonic::Response<super::QueryPacketCommitmentResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Query/PacketCommitment");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " PacketCommitments returns all the packet commitments hashes associated"]
        #[doc = " with a channel."]
        pub async fn packet_commitments(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryPacketCommitmentsRequest>,
        ) -> Result<tonic::Response<super::QueryPacketCommitmentsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/PacketCommitments",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " PacketReceipt queries if a given packet sequence has been received on the queried chain"]
        pub async fn packet_receipt(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryPacketReceiptRequest>,
        ) -> Result<tonic::Response<super::QueryPacketReceiptResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Query/PacketReceipt");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " PacketAcknowledgement queries a stored packet acknowledgement hash."]
        pub async fn packet_acknowledgement(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryPacketAcknowledgementRequest>,
        ) -> Result<tonic::Response<super::QueryPacketAcknowledgementResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/PacketAcknowledgement",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " PacketAcknowledgements returns all the packet acknowledgements associated"]
        #[doc = " with a channel."]
        pub async fn packet_acknowledgements(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryPacketAcknowledgementsRequest>,
        ) -> Result<tonic::Response<super::QueryPacketAcknowledgementsResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/PacketAcknowledgements",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " UnreceivedPackets returns all the unreceived IBC packets associated with a"]
        #[doc = " channel and sequences."]
        pub async fn unreceived_packets(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryUnreceivedPacketsRequest>,
        ) -> Result<tonic::Response<super::QueryUnreceivedPacketsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/UnreceivedPackets",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " UnreceivedAcks returns all the unreceived IBC acknowledgements associated with a"]
        #[doc = " channel and sequences."]
        pub async fn unreceived_acks(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryUnreceivedAcksRequest>,
        ) -> Result<tonic::Response<super::QueryUnreceivedAcksResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Query/UnreceivedAcks");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " NextSequenceReceive returns the next receive sequence for a given channel."]
        pub async fn next_sequence_receive(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryNextSequenceReceiveRequest>,
        ) -> Result<tonic::Response<super::QueryNextSequenceReceiveResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Query/NextSequenceReceive",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
    }
    impl<T: Clone> Clone for QueryClient<T> {
        fn clone(&self) -> Self {
            Self {
                inner: self.inner.clone(),
            }
        }
    }
    impl<T> std::fmt::Debug for QueryClient<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "QueryClient {{ ... }}")
        }
    }
}


use ibc_proto::ibc::core::channel::v1::{
    MsgChannelOpenInit,
    MsgChannelOpenInitResponse,
    MsgChannelOpenTry,
    MsgChannelOpenTryResponse,
    MsgChannelOpenAck,
    MsgChannelOpenAckResponse,
    MsgChannelOpenConfirm,
    MsgChannelOpenConfirmResponse,
    MsgChannelCloseInit,
    MsgChannelCloseInitResponse,
    MsgChannelCloseConfirm,
    MsgChannelCloseConfirmResponse,
    MsgRecvPacket,
    MsgRecvPacketResponse,
    MsgTimeout,
    MsgTimeoutResponse,
    MsgTimeoutOnClose,
    MsgTimeoutOnCloseResponse,
    MsgAcknowledgement,
    MsgAcknowledgementResponse
};

#[doc = r" Generated client implementations."]
pub mod msg_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Msg defines the ibc/channel Msg service."]
    pub struct MsgClient<T> {
        inner: tonic::client::Grpc<T>,
    }
    impl MsgClient<tonic::transport::Channel> {
        #[doc = r" Attempt to create a new client by connecting to a given endpoint."]
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
        T::ResponseBody: Body + HttpBody + Send + 'static,
        T::Error: Into<StdError>,
        <T::ResponseBody as HttpBody>::Error: Into<StdError> + Send,
    {
        pub fn new(inner: T) -> Self {
            let inner = tonic::client::Grpc::new(inner);
            Self { inner }
        }
        pub fn with_interceptor(inner: T, interceptor: impl Into<tonic::Interceptor>) -> Self {
            let inner = tonic::client::Grpc::with_interceptor(inner, interceptor);
            Self { inner }
        }
        #[doc = " ChannelOpenInit defines a rpc handler method for MsgChannelOpenInit."]
        pub async fn channel_open_init(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgChannelOpenInit>,
        ) -> Result<tonic::Response<super::MsgChannelOpenInitResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/ChannelOpenInit");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ChannelOpenTry defines a rpc handler method for MsgChannelOpenTry."]
        pub async fn channel_open_try(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgChannelOpenTry>,
        ) -> Result<tonic::Response<super::MsgChannelOpenTryResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/ChannelOpenTry");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ChannelOpenAck defines a rpc handler method for MsgChannelOpenAck."]
        pub async fn channel_open_ack(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgChannelOpenAck>,
        ) -> Result<tonic::Response<super::MsgChannelOpenAckResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/ChannelOpenAck");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ChannelOpenConfirm defines a rpc handler method for MsgChannelOpenConfirm."]
        pub async fn channel_open_confirm(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgChannelOpenConfirm>,
        ) -> Result<tonic::Response<super::MsgChannelOpenConfirmResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/ChannelOpenConfirm");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ChannelCloseInit defines a rpc handler method for MsgChannelCloseInit."]
        pub async fn channel_close_init(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgChannelCloseInit>,
        ) -> Result<tonic::Response<super::MsgChannelCloseInitResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/ChannelCloseInit");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ChannelCloseConfirm defines a rpc handler method for MsgChannelCloseConfirm."]
        pub async fn channel_close_confirm(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgChannelCloseConfirm>,
        ) -> Result<tonic::Response<super::MsgChannelCloseConfirmResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.channel.v1.Msg/ChannelCloseConfirm",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " RecvPacket defines a rpc handler method for MsgRecvPacket."]
        pub async fn recv_packet(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgRecvPacket>,
        ) -> Result<tonic::Response<super::MsgRecvPacketResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/RecvPacket");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Timeout defines a rpc handler method for MsgTimeout."]
        pub async fn timeout(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgTimeout>,
        ) -> Result<tonic::Response<super::MsgTimeoutResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/Timeout");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " TimeoutOnClose defines a rpc handler method for MsgTimeoutOnClose."]
        pub async fn timeout_on_close(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgTimeoutOnClose>,
        ) -> Result<tonic::Response<super::MsgTimeoutOnCloseResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/TimeoutOnClose");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Acknowledgement defines a rpc handler method for MsgAcknowledgement."]
        pub async fn acknowledgement(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgAcknowledgement>,
        ) -> Result<tonic::Response<super::MsgAcknowledgementResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.channel.v1.Msg/Acknowledgement");
            self.inner.unary(request.into_request(), path, codec).await
        }
    }
    impl<T: Clone> Clone for MsgClient<T> {
        fn clone(&self) -> Self {
            Self {
                inner: self.inner.clone(),
            }
        }
    }
    impl<T> std::fmt::Debug for MsgClient<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "MsgClient {{ ... }}")
        }
    }
}

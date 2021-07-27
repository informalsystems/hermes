use ibc_proto::ibc::core::connection::v1::{
    QueryConnectionRequest,
    QueryConnectionResponse,
    QueryConnectionsRequest,
    QueryConnectionsResponse,
    QueryClientConnectionsRequest,
    QueryClientConnectionsResponse,
    QueryConnectionClientStateRequest,
    QueryConnectionClientStateResponse,
    QueryConnectionConsensusStateRequest,
    QueryConnectionConsensusStateResponse,






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
        #[doc = " Connection queries an IBC connection end."]
        pub async fn connection(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryConnectionRequest>,
        ) -> Result<tonic::Response<super::QueryConnectionResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.connection.v1.Query/Connection");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Connections queries all the IBC connections of a chain."]
        pub async fn connections(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryConnectionsRequest>,
        ) -> Result<tonic::Response<super::QueryConnectionsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/ibc.core.connection.v1.Query/Connections");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ClientConnections queries the connection paths associated with a client"]
        #[doc = " state."]
        pub async fn client_connections(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryClientConnectionsRequest>,
        ) -> Result<tonic::Response<super::QueryClientConnectionsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.connection.v1.Query/ClientConnections",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ConnectionClientState queries the client state associated with the"]
        #[doc = " connection."]
        pub async fn connection_client_state(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryConnectionClientStateRequest>,
        ) -> Result<tonic::Response<super::QueryConnectionClientStateResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.connection.v1.Query/ConnectionClientState",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ConnectionConsensusState queries the consensus state associated with the"]
        #[doc = " connection."]
        pub async fn connection_consensus_state(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryConnectionConsensusStateRequest>,
        ) -> Result<tonic::Response<super::QueryConnectionConsensusStateResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.connection.v1.Query/ConnectionConsensusState",
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


use ibc_proto::ibc::core::connection::v1::{
    MsgConnectionOpenInit,
    MsgConnectionOpenInitResponse,
    MsgConnectionOpenTry,
    MsgConnectionOpenTryResponse,
    MsgConnectionOpenAck,
    MsgConnectionOpenAckResponse,
    MsgConnectionOpenConfirm,
    MsgConnectionOpenConfirmResponse,
};

#[doc = r" Generated client implementations."]
pub mod msg_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Msg defines the ibc/connection Msg service."]
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
        #[doc = " ConnectionOpenInit defines a rpc handler method for MsgConnectionOpenInit."]
        pub async fn connection_open_init(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgConnectionOpenInit>,
        ) -> Result<tonic::Response<super::MsgConnectionOpenInitResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.connection.v1.Msg/ConnectionOpenInit",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ConnectionOpenTry defines a rpc handler method for MsgConnectionOpenTry."]
        pub async fn connection_open_try(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgConnectionOpenTry>,
        ) -> Result<tonic::Response<super::MsgConnectionOpenTryResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.connection.v1.Msg/ConnectionOpenTry",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ConnectionOpenAck defines a rpc handler method for MsgConnectionOpenAck."]
        pub async fn connection_open_ack(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgConnectionOpenAck>,
        ) -> Result<tonic::Response<super::MsgConnectionOpenAckResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.connection.v1.Msg/ConnectionOpenAck",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ConnectionOpenConfirm defines a rpc handler method for MsgConnectionOpenConfirm."]
        pub async fn connection_open_confirm(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgConnectionOpenConfirm>,
        ) -> Result<tonic::Response<super::MsgConnectionOpenConfirmResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/ibc.core.connection.v1.Msg/ConnectionOpenConfirm",
            );
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

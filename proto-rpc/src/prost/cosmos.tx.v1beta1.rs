use ibc_proto::cosmos::tx::v1beta1::{
    SimulateRequest,
    SimulateResponse,
    GetTxRequest,
    GetTxResponse,
    BroadcastTxRequest,
    BroadcastTxResponse,
    GetTxsEventRequest,
    GetTxsEventResponse
};

#[doc = r" Generated client implementations."]
pub mod service_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Service defines a gRPC service for interacting with transactions."]
    pub struct ServiceClient<T> {
        inner: tonic::client::Grpc<T>,
    }
    impl ServiceClient<tonic::transport::Channel> {
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
    impl<T> ServiceClient<T>
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
        #[doc = " Simulate simulates executing a transaction for estimating gas usage."]
        pub async fn simulate(
            &mut self,
            request: impl tonic::IntoRequest<super::SimulateRequest>,
        ) -> Result<tonic::Response<super::SimulateResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/cosmos.tx.v1beta1.Service/Simulate");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " GetTx fetches a tx by hash."]
        pub async fn get_tx(
            &mut self,
            request: impl tonic::IntoRequest<super::GetTxRequest>,
        ) -> Result<tonic::Response<super::GetTxResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/cosmos.tx.v1beta1.Service/GetTx");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " BroadcastTx broadcast transaction."]
        pub async fn broadcast_tx(
            &mut self,
            request: impl tonic::IntoRequest<super::BroadcastTxRequest>,
        ) -> Result<tonic::Response<super::BroadcastTxResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.tx.v1beta1.Service/BroadcastTx");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " GetTxsEvent fetches txs by event."]
        pub async fn get_txs_event(
            &mut self,
            request: impl tonic::IntoRequest<super::GetTxsEventRequest>,
        ) -> Result<tonic::Response<super::GetTxsEventResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.tx.v1beta1.Service/GetTxsEvent");
            self.inner.unary(request.into_request(), path, codec).await
        }
    }
    impl<T: Clone> Clone for ServiceClient<T> {
        fn clone(&self) -> Self {
            Self {
                inner: self.inner.clone(),
            }
        }
    }
    impl<T> std::fmt::Debug for ServiceClient<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "ServiceClient {{ ... }}")
        }
    }
}

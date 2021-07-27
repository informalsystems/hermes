use ibc_proto::cosmos::base::tendermint::v1beta1::{
    GetNodeInfoRequest,
    GetNodeInfoResponse,
    GetSyncingRequest,
    GetSyncingResponse,
    GetLatestBlockRequest,
    GetLatestBlockResponse,
    GetBlockByHeightRequest,
    GetBlockByHeightResponse,
    GetLatestValidatorSetRequest,
    GetLatestValidatorSetResponse,
    GetValidatorSetByHeightRequest,
    GetValidatorSetByHeightResponse
};

#[doc = r" Generated client implementations."]
pub mod service_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Service defines the gRPC querier service for tendermint queries."]
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
        #[doc = " GetNodeInfo queries the current node info."]
        pub async fn get_node_info(
            &mut self,
            request: impl tonic::IntoRequest<super::GetNodeInfoRequest>,
        ) -> Result<tonic::Response<super::GetNodeInfoResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.base.tendermint.v1beta1.Service/GetNodeInfo",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " GetSyncing queries node syncing."]
        pub async fn get_syncing(
            &mut self,
            request: impl tonic::IntoRequest<super::GetSyncingRequest>,
        ) -> Result<tonic::Response<super::GetSyncingResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.base.tendermint.v1beta1.Service/GetSyncing",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " GetLatestBlock returns the latest block."]
        pub async fn get_latest_block(
            &mut self,
            request: impl tonic::IntoRequest<super::GetLatestBlockRequest>,
        ) -> Result<tonic::Response<super::GetLatestBlockResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.base.tendermint.v1beta1.Service/GetLatestBlock",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " GetBlockByHeight queries block for given height."]
        pub async fn get_block_by_height(
            &mut self,
            request: impl tonic::IntoRequest<super::GetBlockByHeightRequest>,
        ) -> Result<tonic::Response<super::GetBlockByHeightResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.base.tendermint.v1beta1.Service/GetBlockByHeight",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " GetLatestValidatorSet queries latest validator-set."]
        pub async fn get_latest_validator_set(
            &mut self,
            request: impl tonic::IntoRequest<super::GetLatestValidatorSetRequest>,
        ) -> Result<tonic::Response<super::GetLatestValidatorSetResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.base.tendermint.v1beta1.Service/GetLatestValidatorSet",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " GetValidatorSetByHeight queries validator-set at a given height."]
        pub async fn get_validator_set_by_height(
            &mut self,
            request: impl tonic::IntoRequest<super::GetValidatorSetByHeightRequest>,
        ) -> Result<tonic::Response<super::GetValidatorSetByHeightResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.base.tendermint.v1beta1.Service/GetValidatorSetByHeight",
            );
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

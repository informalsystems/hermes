use ibc_proto::cosmos::upgrade::v1beta1::{
    QueryCurrentPlanRequest,
    QueryCurrentPlanResponse,
    QueryAppliedPlanRequest,
    QueryAppliedPlanResponse,
    QueryUpgradedConsensusStateRequest,
    QueryUpgradedConsensusStateResponse
};

#[doc = r" Generated client implementations."]
pub mod query_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Query defines the gRPC upgrade querier service."]
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
        #[doc = " CurrentPlan queries the current upgrade plan."]
        pub async fn current_plan(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryCurrentPlanRequest>,
        ) -> Result<tonic::Response<super::QueryCurrentPlanResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.upgrade.v1beta1.Query/CurrentPlan");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " AppliedPlan queries a previously applied upgrade plan by its name."]
        pub async fn applied_plan(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryAppliedPlanRequest>,
        ) -> Result<tonic::Response<super::QueryAppliedPlanResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.upgrade.v1beta1.Query/AppliedPlan");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " UpgradedConsensusState queries the consensus state that will serve"]
        #[doc = " as a trusted kernel for the next version of this chain. It will only be"]
        #[doc = " stored at the last height of this chain."]
        #[doc = " UpgradedConsensusState RPC not supported with legacy querier"]
        pub async fn upgraded_consensus_state(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryUpgradedConsensusStateRequest>,
        ) -> Result<tonic::Response<super::QueryUpgradedConsensusStateResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.upgrade.v1beta1.Query/UpgradedConsensusState",
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

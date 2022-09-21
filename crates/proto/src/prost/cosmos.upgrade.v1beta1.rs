/// Plan specifies information about a planned upgrade and when it should occur.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Plan {
    /// Sets the name for the upgrade. This name will be used by the upgraded
    /// version of the software to apply any special "on-upgrade" commands during
    /// the first BeginBlock method after the upgrade is applied. It is also used
    /// to detect whether a software version can handle a given upgrade. If no
    /// upgrade handler with this name has been set in the software, it will be
    /// assumed that the software is out-of-date when the upgrade Time or Height is
    /// reached and the software will exit.
    #[prost(string, tag="1")]
    pub name: ::prost::alloc::string::String,
    /// Deprecated: Time based upgrades have been deprecated. Time based upgrade logic
    /// has been removed from the SDK.
    /// If this field is not empty, an error will be thrown.
    #[deprecated]
    #[prost(message, optional, tag="2")]
    pub time: ::core::option::Option<super::super::super::google::protobuf::Timestamp>,
    /// The height at which the upgrade must be performed.
    /// Only used if Time is not set.
    #[prost(int64, tag="3")]
    pub height: i64,
    /// Any application specific upgrade info to be included on-chain
    /// such as a git commit that validators could automatically upgrade to
    #[prost(string, tag="4")]
    pub info: ::prost::alloc::string::String,
    /// Deprecated: UpgradedClientState field has been deprecated. IBC upgrade logic has been
    /// moved to the IBC module in the sub module 02-client.
    /// If this field is not empty, an error will be thrown.
    #[deprecated]
    #[prost(message, optional, tag="5")]
    pub upgraded_client_state: ::core::option::Option<super::super::super::google::protobuf::Any>,
}
/// SoftwareUpgradeProposal is a gov Content type for initiating a software
/// upgrade.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SoftwareUpgradeProposal {
    #[prost(string, tag="1")]
    pub title: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub description: ::prost::alloc::string::String,
    #[prost(message, optional, tag="3")]
    pub plan: ::core::option::Option<Plan>,
}
/// CancelSoftwareUpgradeProposal is a gov Content type for cancelling a software
/// upgrade.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CancelSoftwareUpgradeProposal {
    #[prost(string, tag="1")]
    pub title: ::prost::alloc::string::String,
    #[prost(string, tag="2")]
    pub description: ::prost::alloc::string::String,
}
/// ModuleVersion specifies a module and its consensus version.
///
/// Since: cosmos-sdk 0.43
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ModuleVersion {
    /// name of the app module
    #[prost(string, tag="1")]
    pub name: ::prost::alloc::string::String,
    /// consensus version of the app module
    #[prost(uint64, tag="2")]
    pub version: u64,
}
/// QueryCurrentPlanRequest is the request type for the Query/CurrentPlan RPC
/// method.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCurrentPlanRequest {
}
/// QueryCurrentPlanResponse is the response type for the Query/CurrentPlan RPC
/// method.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryCurrentPlanResponse {
    /// plan is the current upgrade plan.
    #[prost(message, optional, tag="1")]
    pub plan: ::core::option::Option<Plan>,
}
/// QueryCurrentPlanRequest is the request type for the Query/AppliedPlan RPC
/// method.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryAppliedPlanRequest {
    /// name is the name of the applied plan to query for.
    #[prost(string, tag="1")]
    pub name: ::prost::alloc::string::String,
}
/// QueryAppliedPlanResponse is the response type for the Query/AppliedPlan RPC
/// method.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryAppliedPlanResponse {
    /// height is the block height at which the plan was applied.
    #[prost(int64, tag="1")]
    pub height: i64,
}
/// QueryUpgradedConsensusStateRequest is the request type for the Query/UpgradedConsensusState
/// RPC method.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUpgradedConsensusStateRequest {
    /// last height of the current chain must be sent in request
    /// as this is the height under which next consensus state is stored
    #[prost(int64, tag="1")]
    pub last_height: i64,
}
/// QueryUpgradedConsensusStateResponse is the response type for the Query/UpgradedConsensusState
/// RPC method.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryUpgradedConsensusStateResponse {
    /// Since: cosmos-sdk 0.43
    #[prost(bytes="vec", tag="2")]
    pub upgraded_consensus_state: ::prost::alloc::vec::Vec<u8>,
}
/// QueryModuleVersionsRequest is the request type for the Query/ModuleVersions
/// RPC method.
///
/// Since: cosmos-sdk 0.43
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryModuleVersionsRequest {
    /// module_name is a field to query a specific module
    /// consensus version from state. Leaving this empty will
    /// fetch the full list of module versions from state
    #[prost(string, tag="1")]
    pub module_name: ::prost::alloc::string::String,
}
/// QueryModuleVersionsResponse is the response type for the Query/ModuleVersions
/// RPC method.
///
/// Since: cosmos-sdk 0.43
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct QueryModuleVersionsResponse {
    /// module_versions is a list of module names with their consensus versions.
    #[prost(message, repeated, tag="1")]
    pub module_versions: ::prost::alloc::vec::Vec<ModuleVersion>,
}
/// Generated client implementations.
#[cfg(feature = "client")]
pub mod query_client {
    #![allow(unused_variables, dead_code, missing_docs, clippy::let_unit_value)]
    use tonic::codegen::*;
    use tonic::codegen::http::Uri;
    /// Query defines the gRPC upgrade querier service.
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
        T::ResponseBody: Body<Data = Bytes> + Send + 'static,
        <T::ResponseBody as Body>::Error: Into<StdError> + Send,
    {
        pub fn new(inner: T) -> Self {
            let inner = tonic::client::Grpc::new(inner);
            Self { inner }
        }
        pub fn with_origin(inner: T, origin: Uri) -> Self {
            let inner = tonic::client::Grpc::with_origin(inner, origin);
            Self { inner }
        }
        pub fn with_interceptor<F>(
            inner: T,
            interceptor: F,
        ) -> QueryClient<InterceptedService<T, F>>
        where
            F: tonic::service::Interceptor,
            T::ResponseBody: Default,
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
        /// Compress requests with the given encoding.
        ///
        /// This requires the server to support it otherwise it might respond with an
        /// error.
        #[must_use]
        pub fn send_compressed(mut self, encoding: CompressionEncoding) -> Self {
            self.inner = self.inner.send_compressed(encoding);
            self
        }
        /// Enable decompressing responses.
        #[must_use]
        pub fn accept_compressed(mut self, encoding: CompressionEncoding) -> Self {
            self.inner = self.inner.accept_compressed(encoding);
            self
        }
        /// CurrentPlan queries the current upgrade plan.
        pub async fn current_plan(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryCurrentPlanRequest>,
        ) -> Result<tonic::Response<super::QueryCurrentPlanResponse>, tonic::Status> {
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
                "/cosmos.upgrade.v1beta1.Query/CurrentPlan",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// AppliedPlan queries a previously applied upgrade plan by its name.
        pub async fn applied_plan(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryAppliedPlanRequest>,
        ) -> Result<tonic::Response<super::QueryAppliedPlanResponse>, tonic::Status> {
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
                "/cosmos.upgrade.v1beta1.Query/AppliedPlan",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// UpgradedConsensusState queries the consensus state that will serve
        /// as a trusted kernel for the next version of this chain. It will only be
        /// stored at the last height of this chain.
        /// UpgradedConsensusState RPC not supported with legacy querier
        /// This rpc is deprecated now that IBC has its own replacement
        /// (https://github.com/cosmos/ibc-go/blob/2c880a22e9f9cc75f62b527ca94aa75ce1106001/proto/ibc/core/client/v1/query.proto#L54)
        pub async fn upgraded_consensus_state(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryUpgradedConsensusStateRequest>,
        ) -> Result<
            tonic::Response<super::QueryUpgradedConsensusStateResponse>,
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
                "/cosmos.upgrade.v1beta1.Query/UpgradedConsensusState",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        /// ModuleVersions queries the list of module versions from state.
        ///
        /// Since: cosmos-sdk 0.43
        pub async fn module_versions(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryModuleVersionsRequest>,
        ) -> Result<tonic::Response<super::QueryModuleVersionsResponse>, tonic::Status> {
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
                "/cosmos.upgrade.v1beta1.Query/ModuleVersions",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
    }
}
/// Generated server implementations.
#[cfg(feature = "server")]
pub mod query_server {
    #![allow(unused_variables, dead_code, missing_docs, clippy::let_unit_value)]
    use tonic::codegen::*;
    ///Generated trait containing gRPC methods that should be implemented for use with QueryServer.
    #[async_trait]
    pub trait Query: Send + Sync + 'static {
        /// CurrentPlan queries the current upgrade plan.
        async fn current_plan(
            &self,
            request: tonic::Request<super::QueryCurrentPlanRequest>,
        ) -> Result<tonic::Response<super::QueryCurrentPlanResponse>, tonic::Status>;
        /// AppliedPlan queries a previously applied upgrade plan by its name.
        async fn applied_plan(
            &self,
            request: tonic::Request<super::QueryAppliedPlanRequest>,
        ) -> Result<tonic::Response<super::QueryAppliedPlanResponse>, tonic::Status>;
        /// UpgradedConsensusState queries the consensus state that will serve
        /// as a trusted kernel for the next version of this chain. It will only be
        /// stored at the last height of this chain.
        /// UpgradedConsensusState RPC not supported with legacy querier
        /// This rpc is deprecated now that IBC has its own replacement
        /// (https://github.com/cosmos/ibc-go/blob/2c880a22e9f9cc75f62b527ca94aa75ce1106001/proto/ibc/core/client/v1/query.proto#L54)
        async fn upgraded_consensus_state(
            &self,
            request: tonic::Request<super::QueryUpgradedConsensusStateRequest>,
        ) -> Result<
            tonic::Response<super::QueryUpgradedConsensusStateResponse>,
            tonic::Status,
        >;
        /// ModuleVersions queries the list of module versions from state.
        ///
        /// Since: cosmos-sdk 0.43
        async fn module_versions(
            &self,
            request: tonic::Request<super::QueryModuleVersionsRequest>,
        ) -> Result<tonic::Response<super::QueryModuleVersionsResponse>, tonic::Status>;
    }
    /// Query defines the gRPC upgrade querier service.
    #[derive(Debug)]
    pub struct QueryServer<T: Query> {
        inner: _Inner<T>,
        accept_compression_encodings: EnabledCompressionEncodings,
        send_compression_encodings: EnabledCompressionEncodings,
    }
    struct _Inner<T>(Arc<T>);
    impl<T: Query> QueryServer<T> {
        pub fn new(inner: T) -> Self {
            Self::from_arc(Arc::new(inner))
        }
        pub fn from_arc(inner: Arc<T>) -> Self {
            let inner = _Inner(inner);
            Self {
                inner,
                accept_compression_encodings: Default::default(),
                send_compression_encodings: Default::default(),
            }
        }
        pub fn with_interceptor<F>(
            inner: T,
            interceptor: F,
        ) -> InterceptedService<Self, F>
        where
            F: tonic::service::Interceptor,
        {
            InterceptedService::new(Self::new(inner), interceptor)
        }
        /// Enable decompressing requests with the given encoding.
        #[must_use]
        pub fn accept_compressed(mut self, encoding: CompressionEncoding) -> Self {
            self.accept_compression_encodings.enable(encoding);
            self
        }
        /// Compress responses with the given encoding, if the client supports it.
        #[must_use]
        pub fn send_compressed(mut self, encoding: CompressionEncoding) -> Self {
            self.send_compression_encodings.enable(encoding);
            self
        }
    }
    impl<T, B> tonic::codegen::Service<http::Request<B>> for QueryServer<T>
    where
        T: Query,
        B: Body + Send + 'static,
        B::Error: Into<StdError> + Send + 'static,
    {
        type Response = http::Response<tonic::body::BoxBody>;
        type Error = std::convert::Infallible;
        type Future = BoxFuture<Self::Response, Self::Error>;
        fn poll_ready(
            &mut self,
            _cx: &mut Context<'_>,
        ) -> Poll<Result<(), Self::Error>> {
            Poll::Ready(Ok(()))
        }
        fn call(&mut self, req: http::Request<B>) -> Self::Future {
            let inner = self.inner.clone();
            match req.uri().path() {
                "/cosmos.upgrade.v1beta1.Query/CurrentPlan" => {
                    #[allow(non_camel_case_types)]
                    struct CurrentPlanSvc<T: Query>(pub Arc<T>);
                    impl<
                        T: Query,
                    > tonic::server::UnaryService<super::QueryCurrentPlanRequest>
                    for CurrentPlanSvc<T> {
                        type Response = super::QueryCurrentPlanResponse;
                        type Future = BoxFuture<
                            tonic::Response<Self::Response>,
                            tonic::Status,
                        >;
                        fn call(
                            &mut self,
                            request: tonic::Request<super::QueryCurrentPlanRequest>,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move {
                                (*inner).current_plan(request).await
                            };
                            Box::pin(fut)
                        }
                    }
                    let accept_compression_encodings = self.accept_compression_encodings;
                    let send_compression_encodings = self.send_compression_encodings;
                    let inner = self.inner.clone();
                    let fut = async move {
                        let inner = inner.0;
                        let method = CurrentPlanSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = tonic::server::Grpc::new(codec)
                            .apply_compression_config(
                                accept_compression_encodings,
                                send_compression_encodings,
                            );
                        let res = grpc.unary(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                "/cosmos.upgrade.v1beta1.Query/AppliedPlan" => {
                    #[allow(non_camel_case_types)]
                    struct AppliedPlanSvc<T: Query>(pub Arc<T>);
                    impl<
                        T: Query,
                    > tonic::server::UnaryService<super::QueryAppliedPlanRequest>
                    for AppliedPlanSvc<T> {
                        type Response = super::QueryAppliedPlanResponse;
                        type Future = BoxFuture<
                            tonic::Response<Self::Response>,
                            tonic::Status,
                        >;
                        fn call(
                            &mut self,
                            request: tonic::Request<super::QueryAppliedPlanRequest>,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move {
                                (*inner).applied_plan(request).await
                            };
                            Box::pin(fut)
                        }
                    }
                    let accept_compression_encodings = self.accept_compression_encodings;
                    let send_compression_encodings = self.send_compression_encodings;
                    let inner = self.inner.clone();
                    let fut = async move {
                        let inner = inner.0;
                        let method = AppliedPlanSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = tonic::server::Grpc::new(codec)
                            .apply_compression_config(
                                accept_compression_encodings,
                                send_compression_encodings,
                            );
                        let res = grpc.unary(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                "/cosmos.upgrade.v1beta1.Query/UpgradedConsensusState" => {
                    #[allow(non_camel_case_types)]
                    struct UpgradedConsensusStateSvc<T: Query>(pub Arc<T>);
                    impl<
                        T: Query,
                    > tonic::server::UnaryService<
                        super::QueryUpgradedConsensusStateRequest,
                    > for UpgradedConsensusStateSvc<T> {
                        type Response = super::QueryUpgradedConsensusStateResponse;
                        type Future = BoxFuture<
                            tonic::Response<Self::Response>,
                            tonic::Status,
                        >;
                        fn call(
                            &mut self,
                            request: tonic::Request<
                                super::QueryUpgradedConsensusStateRequest,
                            >,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move {
                                (*inner).upgraded_consensus_state(request).await
                            };
                            Box::pin(fut)
                        }
                    }
                    let accept_compression_encodings = self.accept_compression_encodings;
                    let send_compression_encodings = self.send_compression_encodings;
                    let inner = self.inner.clone();
                    let fut = async move {
                        let inner = inner.0;
                        let method = UpgradedConsensusStateSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = tonic::server::Grpc::new(codec)
                            .apply_compression_config(
                                accept_compression_encodings,
                                send_compression_encodings,
                            );
                        let res = grpc.unary(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                "/cosmos.upgrade.v1beta1.Query/ModuleVersions" => {
                    #[allow(non_camel_case_types)]
                    struct ModuleVersionsSvc<T: Query>(pub Arc<T>);
                    impl<
                        T: Query,
                    > tonic::server::UnaryService<super::QueryModuleVersionsRequest>
                    for ModuleVersionsSvc<T> {
                        type Response = super::QueryModuleVersionsResponse;
                        type Future = BoxFuture<
                            tonic::Response<Self::Response>,
                            tonic::Status,
                        >;
                        fn call(
                            &mut self,
                            request: tonic::Request<super::QueryModuleVersionsRequest>,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move {
                                (*inner).module_versions(request).await
                            };
                            Box::pin(fut)
                        }
                    }
                    let accept_compression_encodings = self.accept_compression_encodings;
                    let send_compression_encodings = self.send_compression_encodings;
                    let inner = self.inner.clone();
                    let fut = async move {
                        let inner = inner.0;
                        let method = ModuleVersionsSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = tonic::server::Grpc::new(codec)
                            .apply_compression_config(
                                accept_compression_encodings,
                                send_compression_encodings,
                            );
                        let res = grpc.unary(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                _ => {
                    Box::pin(async move {
                        Ok(
                            http::Response::builder()
                                .status(200)
                                .header("grpc-status", "12")
                                .header("content-type", "application/grpc")
                                .body(empty_body())
                                .unwrap(),
                        )
                    })
                }
            }
        }
    }
    impl<T: Query> Clone for QueryServer<T> {
        fn clone(&self) -> Self {
            let inner = self.inner.clone();
            Self {
                inner,
                accept_compression_encodings: self.accept_compression_encodings,
                send_compression_encodings: self.send_compression_encodings,
            }
        }
    }
    impl<T: Query> Clone for _Inner<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }
    impl<T: std::fmt::Debug> std::fmt::Debug for _Inner<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{:?}", self.0)
        }
    }
    impl<T: Query> tonic::server::NamedService for QueryServer<T> {
        const NAME: &'static str = "cosmos.upgrade.v1beta1.Query";
    }
}

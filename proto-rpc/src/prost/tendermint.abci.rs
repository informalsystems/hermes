#[doc = r" Generated client implementations."]
pub mod abci_application_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    pub struct AbciApplicationClient<T> {
        inner: tonic::client::Grpc<T>,
    }
    impl AbciApplicationClient<tonic::transport::Channel> {
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
    impl<T> AbciApplicationClient<T>
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
        pub async fn echo(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestEcho>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseEcho>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/Echo");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn flush(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestFlush>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseFlush>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/Flush");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn info(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestInfo>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseInfo>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/Info");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn set_option(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestSetOption>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseSetOption>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/SetOption");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn deliver_tx(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestDeliverTx>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseDeliverTx>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/DeliverTx");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn check_tx(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestCheckTx>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseCheckTx>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/CheckTx");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn query(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestQuery>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseQuery>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/Query");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn commit(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestCommit>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseCommit>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/Commit");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn init_chain(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestInitChain>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseInitChain>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/InitChain");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn begin_block(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestBeginBlock>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseBeginBlock>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/BeginBlock");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn end_block(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestEndBlock>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseEndBlock>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/tendermint.abci.ABCIApplication/EndBlock");
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn list_snapshots(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestListSnapshots>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseListSnapshots>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/tendermint.abci.ABCIApplication/ListSnapshots",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn offer_snapshot(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestOfferSnapshot>,
        ) -> Result<tonic::Response<::tendermint_proto::abci::ResponseOfferSnapshot>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/tendermint.abci.ABCIApplication/OfferSnapshot",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn load_snapshot_chunk(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestLoadSnapshotChunk>,
        ) -> Result<
            tonic::Response<::tendermint_proto::abci::ResponseLoadSnapshotChunk>,
            tonic::Status,
        > {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/tendermint.abci.ABCIApplication/LoadSnapshotChunk",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        pub async fn apply_snapshot_chunk(
            &mut self,
            request: impl tonic::IntoRequest<::tendermint_proto::abci::RequestApplySnapshotChunk>,
        ) -> Result<
            tonic::Response<::tendermint_proto::abci::ResponseApplySnapshotChunk>,
            tonic::Status,
        > {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/tendermint.abci.ABCIApplication/ApplySnapshotChunk",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
    }
    impl<T: Clone> Clone for AbciApplicationClient<T> {
        fn clone(&self) -> Self {
            Self {
                inner: self.inner.clone(),
            }
        }
    }
    impl<T> std::fmt::Debug for AbciApplicationClient<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "AbciApplicationClient {{ ... }}")
        }
    }
}

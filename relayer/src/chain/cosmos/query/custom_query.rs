use crate::chain::cosmos::query::{abci_query};
use std::str::FromStr;
use tonic::codegen::{Body, Bytes, http, StdError};
use tonic::IntoRequest;

#[derive(Debug, Clone)]
pub struct QueryClient<T> {
    inner: tonic::client::Grpc<T>,
}

impl QueryClient<tonic::transport::Channel> {
    pub async fn connect<D>(dst: D) -> Result<Self, tonic::transport::Error>
        where
            D: TryInto<tonic::transport::Endpoint>,
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
        T::ResponseBody: Body<Data=Bytes> + Send + 'static,
        <T::ResponseBody as Body>::Error: Into<StdError> + Send, {
    pub fn new(inner: T) -> Self {
        let inner = tonic::client::Grpc::new(inner);
        Self { inner }
    }

    pub async fn query<Q, R>(&mut self, path: &str, param: Q) -> Result<tonic::Response<R>, tonic::Status>
        where Q: Send + Sync + prost::Message + 'static,
              R: prost::Message + Default + 'static {
        self.inner
            .ready()
            .await
            .map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service not ready: {}", e.into()),
                )
            })?;
        let codec = tonic::codec::ProstCodec::default();
        let path = http::uri::PathAndQuery::from_str(path).unwrap();
        self.inner.unary(param.into_request(), path, codec).await
    }
}

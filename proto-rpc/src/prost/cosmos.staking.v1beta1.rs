use ibc_proto::cosmos::staking::v1beta1::{
    QueryValidatorsRequest,
    QueryValidatorsResponse,
    QueryValidatorRequest,
    QueryValidatorResponse,
    QueryValidatorDelegationsRequest,
    QueryValidatorDelegationsResponse,
    QueryValidatorUnbondingDelegationsRequest,
    QueryValidatorUnbondingDelegationsResponse,
    QueryDelegationRequest,
    QueryDelegationResponse,
    QueryUnbondingDelegationRequest,
    QueryUnbondingDelegationResponse,
    QueryDelegatorDelegationsRequest,
    QueryDelegatorDelegationsResponse,
    QueryDelegatorUnbondingDelegationsRequest,
    QueryDelegatorUnbondingDelegationsResponse,
    QueryRedelegationsRequest,
    QueryRedelegationsResponse,
    QueryDelegatorValidatorsRequest,
    QueryDelegatorValidatorsResponse,
    QueryDelegatorValidatorRequest,
    QueryDelegatorValidatorResponse,
    QueryHistoricalInfoRequest,
    QueryHistoricalInfoResponse,
    QueryPoolRequest,
    QueryPoolResponse,
    QueryParamsResponse,
    QueryParamsRequest
};

#[doc = r" Generated client implementations."]
pub mod query_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Query defines the gRPC querier service."]
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
        #[doc = " Validators queries all validators that match the given status."]
        pub async fn validators(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryValidatorsRequest>,
        ) -> Result<tonic::Response<super::QueryValidatorsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Query/Validators");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Validator queries validator info for given validator address."]
        pub async fn validator(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryValidatorRequest>,
        ) -> Result<tonic::Response<super::QueryValidatorResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Query/Validator");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ValidatorDelegations queries delegate info for given validator."]
        pub async fn validator_delegations(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryValidatorDelegationsRequest>,
        ) -> Result<tonic::Response<super::QueryValidatorDelegationsResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/ValidatorDelegations",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " ValidatorUnbondingDelegations queries unbonding delegations of a validator."]
        pub async fn validator_unbonding_delegations(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryValidatorUnbondingDelegationsRequest>,
        ) -> Result<tonic::Response<super::QueryValidatorUnbondingDelegationsResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/ValidatorUnbondingDelegations",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Delegation queries delegate info for given validator delegator pair."]
        pub async fn delegation(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryDelegationRequest>,
        ) -> Result<tonic::Response<super::QueryDelegationResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Query/Delegation");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " UnbondingDelegation queries unbonding info for given validator delegator"]
        #[doc = " pair."]
        pub async fn unbonding_delegation(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryUnbondingDelegationRequest>,
        ) -> Result<tonic::Response<super::QueryUnbondingDelegationResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/UnbondingDelegation",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " DelegatorDelegations queries all delegations of a given delegator address."]
        pub async fn delegator_delegations(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryDelegatorDelegationsRequest>,
        ) -> Result<tonic::Response<super::QueryDelegatorDelegationsResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/DelegatorDelegations",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " DelegatorUnbondingDelegations queries all unbonding delegations of a given"]
        #[doc = " delegator address."]
        pub async fn delegator_unbonding_delegations(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryDelegatorUnbondingDelegationsRequest>,
        ) -> Result<tonic::Response<super::QueryDelegatorUnbondingDelegationsResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/DelegatorUnbondingDelegations",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Redelegations queries redelegations of given address."]
        pub async fn redelegations(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryRedelegationsRequest>,
        ) -> Result<tonic::Response<super::QueryRedelegationsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Query/Redelegations");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " DelegatorValidators queries all validators info for given delegator"]
        #[doc = " address."]
        pub async fn delegator_validators(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryDelegatorValidatorsRequest>,
        ) -> Result<tonic::Response<super::QueryDelegatorValidatorsResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/DelegatorValidators",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " DelegatorValidator queries validator info for given delegator validator"]
        #[doc = " pair."]
        pub async fn delegator_validator(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryDelegatorValidatorRequest>,
        ) -> Result<tonic::Response<super::QueryDelegatorValidatorResponse>, tonic::Status>
        {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/DelegatorValidator",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " HistoricalInfo queries the historical info for given height."]
        pub async fn historical_info(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryHistoricalInfoRequest>,
        ) -> Result<tonic::Response<super::QueryHistoricalInfoResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static(
                "/cosmos.staking.v1beta1.Query/HistoricalInfo",
            );
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Pool queries the pool info."]
        pub async fn pool(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryPoolRequest>,
        ) -> Result<tonic::Response<super::QueryPoolResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Query/Pool");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Parameters queries the staking parameters."]
        pub async fn params(
            &mut self,
            request: impl tonic::IntoRequest<super::QueryParamsRequest>,
        ) -> Result<tonic::Response<super::QueryParamsResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Query/Params");
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

use ibc_proto::cosmos::staking::v1beta1::{
    MsgCreateValidator,
    MsgCreateValidatorResponse,
    MsgEditValidator,
    MsgEditValidatorResponse,
    MsgDelegate,
    MsgDelegateResponse,
    MsgBeginRedelegate,
    MsgBeginRedelegateResponse,
    MsgUndelegate,
    MsgUndelegateResponse
};

#[doc = r" Generated client implementations."]
pub mod msg_client {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    #[doc = " Msg defines the staking Msg service."]
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
        #[doc = " CreateValidator defines a method for creating a new validator."]
        pub async fn create_validator(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgCreateValidator>,
        ) -> Result<tonic::Response<super::MsgCreateValidatorResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Msg/CreateValidator");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " EditValidator defines a method for editing an existing validator."]
        pub async fn edit_validator(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgEditValidator>,
        ) -> Result<tonic::Response<super::MsgEditValidatorResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Msg/EditValidator");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Delegate defines a method for performing a delegation of coins"]
        #[doc = " from a delegator to a validator."]
        pub async fn delegate(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgDelegate>,
        ) -> Result<tonic::Response<super::MsgDelegateResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path = http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Msg/Delegate");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " BeginRedelegate defines a method for performing a redelegation"]
        #[doc = " of coins from a delegator and source validator to a destination validator."]
        pub async fn begin_redelegate(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgBeginRedelegate>,
        ) -> Result<tonic::Response<super::MsgBeginRedelegateResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Msg/BeginRedelegate");
            self.inner.unary(request.into_request(), path, codec).await
        }
        #[doc = " Undelegate defines a method for performing an undelegation from a"]
        #[doc = " delegate and a validator."]
        pub async fn undelegate(
            &mut self,
            request: impl tonic::IntoRequest<super::MsgUndelegate>,
        ) -> Result<tonic::Response<super::MsgUndelegateResponse>, tonic::Status> {
            self.inner.ready().await.map_err(|e| {
                tonic::Status::new(
                    tonic::Code::Unknown,
                    format!("Service was not ready: {}", e.into()),
                )
            })?;
            let codec = tonic::codec::ProstCodec::default();
            let path =
                http::uri::PathAndQuery::from_static("/cosmos.staking.v1beta1.Msg/Undelegate");
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

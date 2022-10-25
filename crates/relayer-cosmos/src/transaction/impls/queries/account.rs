use async_trait::async_trait;
use ibc_proto::cosmos::auth::v1beta1::query_client::QueryClient;
use ibc_proto::cosmos::auth::v1beta1::{BaseAccount, QueryAccountRequest};
use ibc_relayer_framework::base::core::traits::error::{HasError, InjectError};
use tonic::transport::Error as TransportError;
use tonic::{Request, Status};

use crate::transaction::impls::decoders::account::CanDecodeAccount;
use crate::transaction::traits::fields::HasGrpcAddress;

#[async_trait]
pub trait CanQueryAccount: HasError {
    async fn query_account(&self, account_address: &str) -> Result<BaseAccount, Self::Error>;
}

pub trait InjectQueryAccountError: HasError {
    fn address_not_found_error(address: &str) -> Self::Error;
}

#[async_trait]
impl<Context> CanQueryAccount for Context
where
    Context: InjectError<Status> + InjectError<TransportError>,
    Context: InjectQueryAccountError,
    Context: HasGrpcAddress,
    Context: CanDecodeAccount,
{
    async fn query_account(&self, account_address: &str) -> Result<BaseAccount, Self::Error> {
        let grpc_address = self.grpc_address();

        let mut client = QueryClient::connect(grpc_address.clone())
            .await
            .map_err(Self::inject_error)?;

        let request = Request::new(QueryAccountRequest {
            address: account_address.to_string(),
        });

        let response = client.account(request).await;

        // Querying for an account might fail, i.e. if the account doesn't actually exist
        let raw_account = match response.map_err(Self::inject_error)?.into_inner().account {
            Some(account) => account,
            None => return Err(Self::address_not_found_error(account_address)),
        };

        let account = self.decode_account(raw_account)?;

        Ok(account)
    }
}
